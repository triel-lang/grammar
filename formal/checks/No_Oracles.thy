(*  Title:      No_Oracles.thy
    Purpose:    No named theorem of the theories of the session TRIEL_Core depends on
                an oracle, except the equations of the Quickcheck generators of
                datatypes.

The theory imports every theory of formal/core/ROOT. The ML block below takes the
theories of TRIEL_Core among the ancestors of this theory (no list of names), and in each
of them every named fact introduced by that theory itself, not by its parents, the facts
of locales included; concealed facts are not checked. Every theorem of every such fact
must depend on no oracle (an unfinished proof or a result of evaluation by the code
generator is one). The build fails if one does, naming the fact and the oracle, if no
theory of TRIEL_Core is found, or if a theory has no named fact that is checked.

One kind of fact is not checked. For a recursive datatype T, the datatype package of
HOL defines the generators of Quickcheck and assumes their termination with the oracle
Pure.skip_proof; their equations are the facts T.full_exhaustive_T.simps and
T.narrowing_T.simps of the theory of T. Such a fact is left out only if its name has
this form, T is a type declared in that theory, and Pure.skip_proof is its only oracle.
A theorem that uses these equations depends on the oracle in turn and fails the check.
The facts left out are listed in the output.

The number of named facts checked in each theory, their sum, and the facts left out are
exported to output/no_oracles.txt. Run, from the root of the repository:

  isabelle build -e -v -d formal/core -D formal/checks
*)

theory No_Oracles
  imports
    TRIEL_Core.TRIEL_Core
    TRIEL_Core.TRIEL_Trace
    TRIEL_Core.TRIEL_Ex
    TRIEL_Core.TRIEL_Terms
    TRIEL_Core.TRIEL_ND
    TRIEL_Core.TRIEL_Breach
    TRIEL_Core.TRIEL_Completions
    TRIEL_Core.TRIEL_Invariants
    TRIEL_Core.TRIEL_Indicators
    TRIEL_Core.TRIEL_Compositions
    TRIEL_Core.TRIEL_Numbers
    TRIEL_Core.TRIEL_Penalty
    TRIEL_Core.TRIEL_Exec
    TRIEL_Core.TRIEL_Signals
begin

ML \<open>
local
  val prefix_core = "TRIEL_Core."

  (* The theories of TRIEL_Core: all ancestors, not only the parents, which leave out
     the imports that are ancestors of other imports. *)
  val theories =
    Theory.ancestors_of \<^theory>
    |> filter (String.isPrefix prefix_core o Context.theory_long_name)
    |> sort_by Context.theory_long_name
  val _ =
    if null theories then error "No theory of TRIEL_Core among the ancestors of No_Oracles"
    else ()

  (* The named facts introduced by the theory itself, without concealed ones. The
     theorems are stored without their theory and are transferred to this one. *)
  fun own_facts thy =
    Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy))
      (Global_Theory.facts_of thy)
    |> map (apsnd (map (Thm.transfer \<^theory>)))

  fun oracle_names oracles = distinct (op =) (map (fn ((oracle, _), _) => oracle) oracles)

  (* The equations of the Quickcheck generators of a datatype T of the theory, whose
     termination the datatype package assumes with the oracle Pure.skip_proof. *)
  fun quickcheck_equations thy (fact, ths) =
    (case Long_Name.explode fact of
      [b, tname, c, "simps"] =>
        b = Long_Name.base_name (Context.theory_long_name thy) andalso
        (c = "full_exhaustive_" ^ tname orelse c = "narrowing_" ^ tname) andalso
        Sign.declared_tyname thy (Long_Name.implode [b, tname]) andalso
        oracle_names (Thm_Deps.all_oracles ths) = ["Pure.skip_proof"]
    | _ => false)

  (* The facts of the theory that depend on an oracle, with the oracles. One traversal
     for the whole theory; the facts are traversed one by one only to name them. *)
  fun check thy =
    let
      val name = Context.theory_long_name thy
      val (left_out, facts) = List.partition (quickcheck_equations thy) (own_facts thy)
      val n = length facts
      val _ = if n = 0 then error ("Theory " ^ name ^ " has no named fact that is checked") else ()
      val bad =
        if null (Thm_Deps.all_oracles (maps #2 facts)) then []
        else
          facts |> map_filter (fn (fact, ths) =>
            (case oracle_names (Thm_Deps.all_oracles ths) of
              [] => NONE
            | oracles => SOME ("Fact " ^ fact ^ " depends on an oracle: " ^ commas oracles)))
    in ((name, n), (bad, map #1 left_out)) end

  (* Every theory is checked before the build fails, so that the error names every
     fact that depends on an oracle. *)
  val results = map check theories
  val bad = maps (#1 o #2) results
  val _ =
    if null bad then ()
    else error (cat_lines ("Named facts of TRIEL_Core that depend on an oracle:" :: bad))

  val counts = map #1 results
  val total = fold (Integer.add o #2) counts 0
  val left_out = maps (#2 o #2) results
  val text =
    cat_lines (map (fn (name, n) => name ^ ": " ^ string_of_int n ^ " facts") counts) ^
      "\n\nTheorems of TRIEL_Core without oracles: " ^ string_of_int total ^ "\n" ^
      "\nNot checked: the equations of the Quickcheck generators of datatypes, which depend\n" ^
      "on the oracle Pure.skip_proof (" ^ string_of_int (length left_out) ^ " facts):\n" ^
      cat_lines (map (prefix "  ") left_out) ^ "\n"
in
  val _ = writeln text
  val _ = Export.export \<^theory> (Path.binding0 (Path.basic "no_oracles.txt")) [XML.Text text]
end
\<close>

end
