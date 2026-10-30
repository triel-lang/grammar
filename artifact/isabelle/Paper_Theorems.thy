(*  Title:      Paper_Theorems.thy
    Purpose:    The theorems of formal/core cited in the paper, and further ones that
                the artifact documents, by their full names; and the definitions that
                the formal sections of the paper restate.

Every name below is looked up by thm. A name that is not a theorem or definition of
TRIEL_Core is an error, and so the build of the session TRIEL_Paper fails. The check at the end fails the
build as well if one of the theorems (the names before the section on definitions)
depends on an oracle (an unfinished proof is one).
The theorems, with their statements, are also exported to output/paper_theorems.txt
by isabelle build -e.
*)

theory Paper_Theorems
  imports
    TRIEL_Core.TRIEL_Core
    TRIEL_Core.TRIEL_Trace
    TRIEL_Core.TRIEL_Ex
    TRIEL_Core.TRIEL_ND
    TRIEL_Core.TRIEL_Terms
    TRIEL_Core.TRIEL_Breach
    TRIEL_Core.TRIEL_Completions
    TRIEL_Core.TRIEL_Invariants
    TRIEL_Core.TRIEL_Indicators
    TRIEL_Core.TRIEL_Compositions
    TRIEL_Core.TRIEL_Exec
begin

section \<open>Finality of verdicts\<close>

thm TRIEL_Breach.ob_verdict_final
thm TRIEL_Breach.pr_verdict_final
thm TRIEL_Invariants.inv_final
thm TRIEL_Invariants.sinv_final
thm TRIEL_Breach.handle_breach_final
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
thm TRIEL_Exec.term_semantics.violation_after_completion

section \<open>Stability of verdicts and its limits\<close>

thm TRIEL_Core.T2_monotone
thm TRIEL_ND.T2_nd_monotone
thm TRIEL_Ex.present_free_equitone
thm TRIEL_Indicators.verdict_stable
thm TRIEL_Indicators.verdict_stable_nd
thm TRIEL_Indicators.cond_equitone
thm TRIEL_Core.T3_present_not_monotone
thm TRIEL_Core.present_flips
thm TRIEL_Indicators.Ex_breaks_stability
thm TRIEL_Core.T3_default_not_monotone
thm TRIEL_Indicators.default_breaks_stability

text \<open>Stability of the verdicts of norms, not only of the values of conditions: the same trace
  read with more data (\<open>data_le\<close>), and the same observations with more data (\<open>obs_le\<close>) in
  the report of the evaluator.\<close>

thm TRIEL_Trace.forbidden_data_mono
thm TRIEL_Breach.pr_verdict_data_mono
thm TRIEL_Breach.pr_verdict_pending_data_mono
thm TRIEL_Breach.ob_verdict_data_indep
thm TRIEL_Breach.may_verdict_data_mono
thm TRIEL_Invariants.sinv_data_mono_le
thm TRIEL_Breach.pr_verdict_present_not_mono
thm TRIEL_Exec.term_line_data_mono
thm TRIEL_Exec.run_data_mono
thm TRIEL_Exec.run_data_mono_decided
thm TRIEL_Exec.run_data_mono_breach
thm TRIEL_Exec.run_data_mono_pending

section \<open>IF and UNLESS\<close>

thm TRIEL_Terms.term_semantics.den_if
thm TRIEL_Terms.term_semantics.if_classical
thm TRIEL_Terms.term_semantics.if_branch_stable
thm TRIEL_Terms.term_semantics.if_undefined_else
thm TRIEL_Trace.unless_if
thm TRIEL_Trace.interleaving_satisfiable

section \<open>References between the elements of a block\<close>

thm TRIEL_Exec.term_semantics.resolve_den
thm TRIEL_Exec.term_semantics.block_den
thm TRIEL_Exec.refs_ok_acyclic

section \<open>Prohibitions and undefined guards\<close>

thm TRIEL_Breach.undefined_guard_blocks_not_breach
thm TRIEL_Breach.enforced_no_breach
thm TRIEL_Breach.enforce_sound
thm TRIEL_Breach.enforce_is_trace
thm TRIEL_Breach.enforce_preserves_time_order
thm TRIEL_Breach.enforce_idempotent
thm TRIEL_Breach.enforce_blocks_exactly
thm TRIEL_Breach.enforce_id_iff
thm TRIEL_Breach.enforce_transparent
thm TRIEL_Breach.enforce_undefined_blocks
thm TRIEL_Breach.enforce_minimal
thm TRIEL_Breach.monitor_decisions_enforce
thm TRIEL_Breach.monitor_decisions_append
thm TRIEL_Breach.blocks_data_mono
thm TRIEL_Breach.blocked_action_data_mono
thm TRIEL_Completions.enforce_allows_sound

section \<open>Completions of the data\<close>

thm TRIEL_Completions.monitor_sound_completions
thm TRIEL_Completions.breach_certain_completions
thm TRIEL_Completions.skip_reading_unsound
thm TRIEL_Completions.absent_false_unsound
thm TRIEL_Completions.kleene_not_complete
thm TRIEL_Completions.kleene_sound_conn
thm TRIEL_Completions.kleene_optimal
thm TRIEL_Completions.compositional_incomplete
thm TRIEL_Completions.stale_quote_completion

section \<open>The composition algebra\<close>

thm TRIEL_Compositions.comp_closure_equitone
thm TRIEL_Compositions.interp_equitone
thm TRIEL_Compositions.cond_fm_correct
thm TRIEL_Compositions.cond_equitone_from_closure
thm TRIEL_Compositions.expr_cond_correct
thm TRIEL_Compositions.expr_cond_Ex_free
thm TRIEL_Compositions.T2_nd_from_closure
thm TRIEL_Compositions.expr_fm_correct
thm TRIEL_Compositions.T2_from_closure
thm TRIEL_Core.T5_present
thm TRIEL_Ex.present_is_Ex
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

section \<open>Definitions used in the paper\<close>

text \<open>The definitions that the formal sections of the paper restate.\<close>

thm TRIEL_Core.info_le_def
thm TRIEL_Core.approx_def
thm TRIEL_Core.evalV.simps
thm TRIEL_Core.eval.simps
thm TRIEL_Breach.window_def
thm TRIEL_Breach.ob_verdict_def
thm TRIEL_Trace.forbidden_def
thm TRIEL_Breach.pr_verdict_def
thm TRIEL_Breach.blocks_def
thm TRIEL_Breach.blocked_action_def
thm TRIEL_Breach.enforce_def
thm TRIEL_Breach.monitor_decisions_def
thm TRIEL_Invariants.inv_eval.simps
thm TRIEL_Trace.data_le_def
thm TRIEL_Exec.obs_le_def
thm TRIEL_Exec.pr_refines.simps
thm TRIEL_Exec.line_refines.simps
thm TRIEL_Ex.equitone_def
thm TRIEL_Completions.completion_def
thm TRIEL_Completions.evalG.simps
thm TRIEL_Completions.sound_conn_def

section \<open>No oracles\<close>

text \<open>The same names once more: none of these theorems may depend on an oracle. The
  statements are exported as \<open>paper_theorems.txt\<close>.\<close>

ML \<open>
local
  val names =
   ["TRIEL_Breach.ob_verdict_final", "TRIEL_Breach.pr_verdict_final",
    "TRIEL_Invariants.inv_final", "TRIEL_Invariants.sinv_final", "TRIEL_Breach.handle_breach_final",
    "TRIEL_Exec.run_final", "TRIEL_Exec.time_order_rejected",
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
    "TRIEL_Exec.term_semantics.violation_after_completion",
    "TRIEL_Core.T2_monotone", "TRIEL_ND.T2_nd_monotone", "TRIEL_Ex.present_free_equitone",
    "TRIEL_Indicators.verdict_stable", "TRIEL_Indicators.verdict_stable_nd",
    "TRIEL_Indicators.cond_equitone", "TRIEL_Core.T3_present_not_monotone", "TRIEL_Core.present_flips",
    "TRIEL_Indicators.Ex_breaks_stability", "TRIEL_Core.T3_default_not_monotone",
    "TRIEL_Indicators.default_breaks_stability",
    "TRIEL_Trace.forbidden_data_mono",
    "TRIEL_Breach.pr_verdict_data_mono", "TRIEL_Breach.pr_verdict_pending_data_mono",
    "TRIEL_Breach.ob_verdict_data_indep", "TRIEL_Breach.may_verdict_data_mono",
    "TRIEL_Invariants.sinv_data_mono_le", "TRIEL_Breach.pr_verdict_present_not_mono",
    "TRIEL_Exec.term_line_data_mono", "TRIEL_Exec.run_data_mono",
    "TRIEL_Exec.run_data_mono_decided", "TRIEL_Exec.run_data_mono_breach",
    "TRIEL_Exec.run_data_mono_pending",
    "TRIEL_Terms.term_semantics.den_if", "TRIEL_Terms.term_semantics.if_classical",
    "TRIEL_Terms.term_semantics.if_branch_stable", "TRIEL_Terms.term_semantics.if_undefined_else",
    "TRIEL_Trace.unless_if", "TRIEL_Trace.interleaving_satisfiable",
    "TRIEL_Exec.term_semantics.resolve_den", "TRIEL_Exec.term_semantics.block_den",
    "TRIEL_Exec.refs_ok_acyclic",
    "TRIEL_Breach.undefined_guard_blocks_not_breach", "TRIEL_Breach.enforced_no_breach",
    "TRIEL_Breach.enforce_sound", "TRIEL_Breach.enforce_is_trace",
    "TRIEL_Breach.enforce_preserves_time_order", "TRIEL_Breach.enforce_idempotent",
    "TRIEL_Breach.enforce_blocks_exactly", "TRIEL_Breach.enforce_id_iff",
    "TRIEL_Breach.enforce_transparent", "TRIEL_Breach.enforce_undefined_blocks",
    "TRIEL_Breach.enforce_minimal", "TRIEL_Breach.monitor_decisions_enforce",
    "TRIEL_Breach.monitor_decisions_append", "TRIEL_Breach.blocks_data_mono",
    "TRIEL_Breach.blocked_action_data_mono", "TRIEL_Completions.enforce_allows_sound",
    "TRIEL_Completions.monitor_sound_completions", "TRIEL_Completions.breach_certain_completions",
    "TRIEL_Completions.skip_reading_unsound", "TRIEL_Completions.absent_false_unsound",
    "TRIEL_Completions.kleene_not_complete", "TRIEL_Completions.kleene_sound_conn",
    "TRIEL_Completions.kleene_optimal", "TRIEL_Completions.compositional_incomplete",
    "TRIEL_Completions.stale_quote_completion",
    "TRIEL_Compositions.comp_closure_equitone", "TRIEL_Compositions.interp_equitone",
    "TRIEL_Compositions.cond_fm_correct", "TRIEL_Compositions.cond_equitone_from_closure",
    "TRIEL_Compositions.expr_cond_correct", "TRIEL_Compositions.expr_cond_Ex_free",
    "TRIEL_Compositions.T2_nd_from_closure", "TRIEL_Compositions.expr_fm_correct",
    "TRIEL_Compositions.T2_from_closure",
    "TRIEL_Core.T5_present", "TRIEL_Ex.present_is_Ex", "TRIEL_Compositions.Ex_R_is_not_eps",
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
