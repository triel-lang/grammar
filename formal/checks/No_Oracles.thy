(*  Title:      No_Oracles.thy
    Purpose:    No named theorem of the theories of the session TRIEL_Core depends on
                an oracle.

The theory imports every theory of formal/core/ROOT. The ML block below takes the
theories of TRIEL_Core among the ancestors of this theory (no list of names), and in each
of them every named fact introduced by that theory itself, not by its parents, the facts
of locales included; concealed facts are not checked. Every theorem of every such fact
must depend on no oracle (an unfinished proof or a result of evaluation by the code
generator is one). The build fails if one does, naming the fact and the oracle, if no
theory of TRIEL_Core is found, or if a theory has no named fact.

The number of named facts of each theory, and their sum, are exported to
output/no_oracles.txt. Run, from the root of the repository:

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

  (* The named facts introduced by the theory itself, without concealed ones. *)
  fun own_facts thy =
    Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy))
      (Global_Theory.facts_of thy)

  fun oracle_names oracles = commas (map (fn ((oracle, _), _) => oracle) oracles)

  fun check thy =
    let
      val name = Context.theory_long_name thy
      val facts = own_facts thy
      val n = length facts
      val _ = if n = 0 then error ("Theory " ^ name ^ " has no named fact") else ()
      (* One traversal for the whole theory; the facts are traversed one by one only to
         name those that depend on an oracle. *)
      val _ =
        if null (Thm_Deps.all_oracles (maps #2 facts)) then ()
        else
          let
            val bad =
              facts |> map_filter (fn (fact, ths) =>
                (case Thm_Deps.all_oracles ths of
                  [] => NONE
                | oracles => SOME ("Fact " ^ fact ^ " depends on an oracle: " ^ oracle_names oracles)))
          in
            error (cat_lines (("Theory " ^ name ^ ": named facts that depend on an oracle") :: bad))
          end
    in (name, n) end

  val counts = map check theories
  val total = fold (Integer.add o #2) counts 0
  val text =
    cat_lines (map (fn (name, n) => name ^ ": " ^ string_of_int n ^ " facts") counts) ^
      "\n\nTheorems of TRIEL_Core without oracles: " ^ string_of_int total ^ "\n"
in
  val _ = writeln text
  val _ = Export.export \<^theory> (Path.binding0 (Path.basic "no_oracles.txt")) [XML.Text text]
end
\<close>

end
