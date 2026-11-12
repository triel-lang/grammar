(*  Title:      No_Oracles.thy
    Purpose:    No named theorem of the theories of formal/core/ROOT depends on an
                oracle, except the equations of the Quickcheck generators
                (full_exhaustive, narrowing) that Isabelle/HOL generates for a datatype.

The theory imports every theory of formal/core/ROOT. The ML block below takes the
theories of TRIEL_Core among the ancestors of this theory (no list of names), and in each
of them every named fact introduced by that theory itself, not by its parents, the facts
of locales included; concealed facts are not checked. Every theorem of every such fact
must depend on no oracle (an unfinished proof or a result of evaluation by the code
generator is one). The build fails if one does, naming the fact and the oracle, if
no theory of TRIEL_Core is found, or if a theory has no named fact that is checked.

The one exception: for a datatype T, the Quickcheck plugins of the datatype package
(quickcheck_full_exhaustive, quickcheck_narrowing) define the generator constants of T as
undefined and assert their equations with the oracle Pure.skip_proof instead of proving
them (Quickcheck_Common.define_functions). A fact is excluded only if its name is
T.full_exhaustive_T.simps or T.narrowing_T.simps in the theory that defines the datatype
T, and its set of oracles is exactly {Pure.skip_proof}. Any other fact with an oracle
fails the build, so no other named fact depends on the excluded facts. For mutually
recursive datatypes T1 and T2 the plugins name the facts differently
(T1_T2.full_exhaustive_T1.simps), and for an auxiliary type of a nested datatype they use
the name full_exhaustive_<auxname>; such facts are not excluded, and the build fails on
them until the rule is extended.

The number of named facts checked in each theory, their sum, and the excluded facts with
their number in each theory are exported to output/no_oracles.txt. Run, from the root of
the repository:

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

  (* The equations of the Quickcheck generators of a datatype T of the theory, which
     HOL asserts with the oracle Pure.skip_proof: the name, the datatype and the set of
     oracles must all be as stated. *)
  fun quickcheck_equations thy (fact, ths) =
    (case Long_Name.explode fact of
      [b, tname, c, "simps"] =>
        b = Long_Name.base_name (Context.theory_long_name thy) andalso
        (c = "full_exhaustive_" ^ tname orelse c = "narrowing_" ^ tname) andalso
        Sign.declared_tyname thy (Long_Name.implode [b, tname]) andalso
        is_some (Ctr_Sugar.ctr_sugar_of_global thy (Long_Name.implode [b, tname])) andalso
        oracle_names (Thm_Deps.all_oracles ths) = ["Pure.skip_proof"]
    | _ => false)

  type result = {name: string, checked: int, bad: string list, excluded: string list}

  (* The facts of the theory that depend on an oracle, with the oracles. One traversal
     for the whole theory; the facts are traversed one by one only to name them. *)
  fun check thy : result =
    let
      val name = Context.theory_long_name thy
      val (excluded, facts) = List.partition (quickcheck_equations thy) (own_facts thy)
      val n = length facts
      val _ = if n = 0 then error ("Theory " ^ name ^ " has no named fact that is checked") else ()
      val bad =
        if null (Thm_Deps.all_oracles (maps #2 facts)) then []
        else
          facts |> map_filter (fn (fact, ths) =>
            (case oracle_names (Thm_Deps.all_oracles ths) of
              [] => NONE
            | oracles => SOME ("Fact " ^ fact ^ " depends on an oracle: " ^ commas oracles)))
    in {name = name, checked = n, bad = bad, excluded = map #1 excluded} end

  (* Every theory is checked before the build fails, so that the error names every
     fact that depends on an oracle. *)
  val results = map check theories
  val bad = maps #bad results
  val _ =
    if null bad then ()
    else error (cat_lines ("Named facts of TRIEL_Core that depend on an oracle:" :: bad))

  val total = fold (Integer.add o #checked) results 0
  val total_excluded = fold (Integer.add o length o #excluded) results 0
  fun excluded_lines ({name, excluded, ...}: result) =
    ("  " ^ name ^ ": " ^ string_of_int (length excluded) ^ " excluded") ::
      map (prefix "    ") excluded
  val text =
    cat_lines (map (fn {name, checked, ...} => name ^ ": " ^ string_of_int checked ^ " facts")
      results) ^
    "\n\nNamed facts of TRIEL_Core without oracles: " ^ string_of_int total ^
      " (excluded: " ^ string_of_int total_excluded ^
      " Quickcheck generator facts with Pure.skip_proof)\n" ^
    "\nExcluded: the equations of the Quickcheck generators (full_exhaustive, narrowing) that\n" ^
    "Isabelle/HOL generates for a datatype of the theory and asserts with the oracle\n" ^
    "Pure.skip_proof; the set of oracles of each is exactly {Pure.skip_proof}.\n" ^
    cat_lines (maps excluded_lines results) ^ "\n"
in
  val _ = writeln text
  val _ = Export.export \<^theory> (Path.binding0 (Path.basic "no_oracles.txt")) [XML.Text text]
end
\<close>

end
