(*  Title:      Paper_Theorems.thy
    Purpose:    The theorems of formal/core cited in the paper, by their full names.

Every name below is looked up by thm. A name that is not a theorem of TRIEL_Core is an
error, and so the build of the session TRIEL_Paper fails. The check at the end fails the
build as well if one of the theorems depends on an oracle (an unfinished proof is one).
The theorems, with their statements, are also exported to output/paper_theorems.txt
by isabelle build -e.
*)

theory Paper_Theorems
  imports
    TRIEL_Core.TRIEL_Core
    TRIEL_Core.TRIEL_Trace
    TRIEL_Core.TRIEL_Terms
    TRIEL_Core.TRIEL_Breach
    TRIEL_Core.TRIEL_Invariants
    TRIEL_Core.TRIEL_Indicators
    TRIEL_Core.TRIEL_Compositions
    TRIEL_Core.TRIEL_Exec
begin

section \<open>Finality of verdicts\<close>

thm TRIEL_Breach.ob_verdict_final
thm TRIEL_Breach.pr_verdict_final
thm TRIEL_Invariants.inv_final
thm TRIEL_Exec.run_final
thm TRIEL_Exec.time_order_rejected

section \<open>Actions and violations in composite terms\<close>

thm TRIEL_Terms.term_semantics.must_then_must_two_actions
thm TRIEL_Terms.term_semantics.violated_reachable
thm TRIEL_Terms.term_semantics.then_mustnot_violated
thm TRIEL_Breach.mustnot_violated_breach
thm TRIEL_Breach.breach_mustnot_violated
thm TRIEL_Exec.status_final
thm TRIEL_Exec.term_semantics.status_sound
thm TRIEL_Exec.term_semantics.violation_over_done
thm TRIEL_Exec.term_semantics.fden_den
thm TRIEL_Exec.term_semantics.then_mustnot_held
thm TRIEL_Exec.term_semantics.then_mustnot_status
thm TRIEL_Exec.term_semantics.status_no_missed_violation
thm TRIEL_Exec.term_semantics.reached_prohibition_watched
thm TRIEL_Exec.term_semantics.then_mustnot_watched
thm TRIEL_Exec.term_semantics.or_mustnot_watched

section \<open>Stability of verdicts and its limits\<close>

thm TRIEL_Indicators.verdict_stable
thm TRIEL_Indicators.verdict_stable_nd
thm TRIEL_Indicators.cond_equitone
thm TRIEL_Core.T3_present_not_monotone
thm TRIEL_Indicators.Ex_breaks_stability
thm TRIEL_Core.T3_default_not_monotone
thm TRIEL_Indicators.default_breaks_stability

section \<open>IF and UNLESS\<close>

thm TRIEL_Terms.term_semantics.den_if
thm TRIEL_Terms.term_semantics.if_classical
thm TRIEL_Terms.term_semantics.if_branch_stable
thm TRIEL_Trace.unless_if

section \<open>References between the elements of a block\<close>

thm TRIEL_Exec.term_semantics.resolve_den
thm TRIEL_Exec.term_semantics.block_den
thm TRIEL_Exec.refs_ok_acyclic

section \<open>Prohibitions and undefined guards\<close>

thm TRIEL_Breach.undefined_guard_blocks_not_breach
thm TRIEL_Breach.enforced_no_breach

section \<open>The composition algebra\<close>

thm TRIEL_Compositions.comp_closure_equitone
thm TRIEL_Compositions.interp_equitone
thm TRIEL_Compositions.cond_fm_correct
thm TRIEL_Compositions.cond_equitone_from_closure
thm TRIEL_Core.T5_present
thm TRIEL_Compositions.Ex_R_is_not_eps

section \<open>Deadlines with ELSE\<close>

thm TRIEL_Breach.else_taken
thm TRIEL_Breach.else_no_breach
thm TRIEL_Breach.else_alt_breached
thm TRIEL_Breach.else_final

section \<open>Hidden data\<close>

thm TRIEL_Exec.run_noninterference
thm TRIEL_Exec.run_erase
thm TRIEL_Exec.erase_flat
thm TRIEL_Exec.flow_safe_eval
thm TRIEL_Exec.flow_safe_evalV

section \<open>No oracles\<close>

text \<open>The same names once more: none of these theorems may depend on an oracle. The
  statements are exported as \<open>paper_theorems.txt\<close>.\<close>

ML \<open>
local
  val names =
   ["TRIEL_Breach.ob_verdict_final", "TRIEL_Breach.pr_verdict_final",
    "TRIEL_Invariants.inv_final", "TRIEL_Exec.run_final", "TRIEL_Exec.time_order_rejected",
    "TRIEL_Terms.term_semantics.must_then_must_two_actions",
    "TRIEL_Terms.term_semantics.violated_reachable",
    "TRIEL_Terms.term_semantics.then_mustnot_violated",
    "TRIEL_Breach.mustnot_violated_breach", "TRIEL_Breach.breach_mustnot_violated",
    "TRIEL_Exec.status_final", "TRIEL_Exec.term_semantics.status_sound",
    "TRIEL_Exec.term_semantics.violation_over_done",
    "TRIEL_Exec.term_semantics.fden_den", "TRIEL_Exec.term_semantics.then_mustnot_held",
    "TRIEL_Exec.term_semantics.then_mustnot_status",
    "TRIEL_Exec.term_semantics.status_no_missed_violation",
    "TRIEL_Exec.term_semantics.reached_prohibition_watched",
    "TRIEL_Exec.term_semantics.then_mustnot_watched", "TRIEL_Exec.term_semantics.or_mustnot_watched",
    "TRIEL_Indicators.verdict_stable", "TRIEL_Indicators.verdict_stable_nd",
    "TRIEL_Indicators.cond_equitone", "TRIEL_Core.T3_present_not_monotone",
    "TRIEL_Indicators.Ex_breaks_stability", "TRIEL_Core.T3_default_not_monotone",
    "TRIEL_Indicators.default_breaks_stability",
    "TRIEL_Terms.term_semantics.den_if", "TRIEL_Terms.term_semantics.if_classical",
    "TRIEL_Terms.term_semantics.if_branch_stable", "TRIEL_Trace.unless_if",
    "TRIEL_Exec.term_semantics.resolve_den", "TRIEL_Exec.term_semantics.block_den",
    "TRIEL_Exec.refs_ok_acyclic",
    "TRIEL_Breach.undefined_guard_blocks_not_breach", "TRIEL_Breach.enforced_no_breach",
    "TRIEL_Compositions.comp_closure_equitone", "TRIEL_Compositions.interp_equitone",
    "TRIEL_Compositions.cond_fm_correct", "TRIEL_Compositions.cond_equitone_from_closure",
    "TRIEL_Core.T5_present", "TRIEL_Compositions.Ex_R_is_not_eps",
    "TRIEL_Breach.else_taken", "TRIEL_Breach.else_no_breach",
    "TRIEL_Breach.else_alt_breached", "TRIEL_Breach.else_final",
    "TRIEL_Exec.run_noninterference", "TRIEL_Exec.run_erase", "TRIEL_Exec.erase_flat",
    "TRIEL_Exec.flow_safe_eval", "TRIEL_Exec.flow_safe_evalV"]
  val ctxt = \<^context>
  fun check name =
    let
      val ths = Proof_Context.get_thms ctxt name
      val oracles = Thm_Deps.all_oracles ths
      val _ =
        if null oracles then ()
        else error ("Theorem " ^ name ^ " depends on an oracle: " ^
          commas (map (fn ((oracle, _), _) => oracle) oracles))
    in
      cat_lines (name :: map (prefix "  " o Pretty.string_of_ops (Pretty.pure_output_ops (SOME 1000)) o Thm.pretty_thm ctxt) ths)
    end
  val text =
    cat_lines (map check names) ^ "\n\nPaper theorems without oracles: " ^
      string_of_int (length names) ^ "\n"
in
  val _ = writeln text
  val _ = Export.export \<^theory> (Path.binding0 (Path.basic "paper_theorems.txt")) [XML.Text text]
end
\<close>

end
