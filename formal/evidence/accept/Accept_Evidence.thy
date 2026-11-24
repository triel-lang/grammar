(*  Title:      Accept_Evidence.thy
    Acceptance of the evidence of the value of a condition. Written by the maintainers, not by
    the stage; the stage may not change this file (its SHA-256 is checked). Each lemma restates a
    theorem of the session TRIEL_Evidence with every type variable carrying its sort, the
    classes named in full (HOL.type, TRIEL_Core.value_order), and proves it by that theorem
    alone. The ML block at the end fails if a lemma uses a constant that is neither of the
    core (with HOL) nor one of the three constants of TRIEL_Evidence_Def named below; if a
    lemma does not use the constants it is about; or if a lemma depends on an Isabelle oracle (an
    unproved assumption; an unfinished proof is one). That TRIEL_Evidence.thy runs no ML of its own, which could
    change what this block sees, is checked before it is built, by Lex_Evidence.thy.
*)

theory Accept_Evidence
  imports TRIEL_Core.TRIEL_Completions TRIEL_Evidence.TRIEL_Evidence
begin

text \<open>The evidence names only names of the condition; read values are present, read absences and missing names are absent.\<close>

lemma accept_names:
  "evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U) \<Longrightarrow> set X \<union> set A \<union> set U \<subseteq> names c \<union> pnames c"
  by (rule evidence_names)

lemma accept_shape:
  "evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U) \<Longrightarrow> set X \<subseteq> dom \<sigma> \<and> set A \<inter> dom \<sigma> = {} \<and> set U \<inter> dom \<sigma> = {}"
  by (rule evidence_shape)

lemma accept_present_free:
  "present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) \<Longrightarrow> evidence c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U) \<Longrightarrow> A = []"
  by (rule evidence_present_free)

text \<open>(a) A defined value waits for nothing, and it is the same in every state that agrees on X and has no value on A, whatever the other data.\<close>

lemma accept_definite_U:
  "\<lbrakk>evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = Some b\<rbrakk> \<Longrightarrow> U = []"
  by (rule evidence_definite_U)

lemma accept_definite:
  "\<lbrakk>evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = Some b; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x; \<forall>x \<in> set A. \<sigma>' x = None\<rbrakk> \<Longrightarrow> eval c \<sigma>' = Some b"
  by (rule evidence_definite)

lemma accept_definite_pf:
  "\<lbrakk>present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr); evidence c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = Some b; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x\<rbrakk> \<Longrightarrow> eval c \<sigma>' = Some b"
  by (rule evidence_definite_pf)

lemma accept_completions:
  "\<lbrakk>present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr); evidence c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = Some b; completion (\<sigma> |` set X) \<sigma>'\<rbrakk> \<Longrightarrow> eval c \<sigma>' = Some b"
  by (rule evidence_completions)

text \<open>(b) An undefined value names what it waits for: those names are absent; in a state that keeps the values of X and the absence of A, while they stay absent it stays undefined, and once all have values it is defined.\<close>

lemma accept_undefined_U:
  "\<lbrakk>evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = None\<rbrakk> \<Longrightarrow> U \<noteq> []"
  by (rule evidence_undefined_U)

lemma accept_undefined_absent:
  "\<lbrakk>evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = None\<rbrakk> \<Longrightarrow> \<forall>x \<in> set U. \<sigma> x = None"
  by (rule evidence_undefined_absent)

lemma accept_undefined_stays:
  "\<lbrakk>evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = None; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x; \<forall>x \<in> set A \<union> set U. \<sigma>' x = None\<rbrakk> \<Longrightarrow> eval c \<sigma>' = None"
  by (rule evidence_undefined_stays)

lemma accept_undefined_resolved:
  "\<lbrakk>evidence (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = None; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x; \<forall>x \<in> set A. \<sigma>' x = None; set U \<subseteq> dom \<sigma>'\<rbrakk> \<Longrightarrow> eval c \<sigma>' \<noteq> None"
  by (rule evidence_undefined_resolved)

lemma accept_undefined_pf:
  "\<lbrakk>present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr); evidence c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = None; \<sigma> \<sqsubseteq> \<sigma>'; set U \<subseteq> dom \<sigma>'\<rbrakk> \<Longrightarrow> eval c \<sigma>' \<noteq> None"
  by (rule evidence_undefined_pf)

text \<open>A supporting set is checked by one evaluation of eval: for a condition without PRESENT and DEFAULT, a set that supports a value keeps it in every state that agrees on the set.\<close>

lemma accept_supports_sound:
  "\<lbrakk>present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr); supports X c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) b; \<forall>x \<in> X. \<sigma>' x = \<sigma> x\<rbrakk> \<Longrightarrow> eval c \<sigma>' = Some b"
  by (rule supports_sound)

lemma accept_supports_mono:
  "\<lbrakk>present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr); X \<subseteq> Y; supports X c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) b\<rbrakk> \<Longrightarrow> supports Y c \<sigma> b"
  by (rule supports_mono)

lemma accept_supports:
  "\<lbrakk>present_free (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr); evidence c (\<sigma> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.state) = (X, A, U); eval c \<sigma> = Some b\<rbrakk> \<Longrightarrow> supports (set X) c \<sigma> b"
  by (rule evidence_supports)

text \<open>On a trace the decisions are those of the monitor; a decision of the monitor and its evidence are final, and a decision with a defined value stays on every trace of the same length with the same event that keeps X and the absence of A in the entry before.\<close>

lemma accept_decisions:
  "map (\<lambda>(j, v, w). (j, v \<noteq> Some False)) (monitor_evidence s a (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<pi> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order, 's :: HOL.type, 'a :: HOL.type) TRIEL_Breach.itrace)) = monitor_decisions s a c \<pi>"
  by (rule monitor_evidence_decisions)

lemma accept_append:
  "\<exists>ws. monitor_evidence s a (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) ((\<pi> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order, 's :: HOL.type, 'a :: HOL.type) TRIEL_Breach.itrace) @ \<rho>) = monitor_evidence s a c \<pi> @ ws"
  by (rule monitor_evidence_append)

lemma accept_stable:
  "\<lbrakk>(j, Some b, (X, A, U)) \<in> set (monitor_evidence s a (c :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order) TRIEL_Core.expr) (\<pi> :: ('n :: HOL.type, 'v :: TRIEL_Core.value_order, 's :: HOL.type, 'a :: HOL.type) TRIEL_Breach.itrace)); length \<pi>' = length \<pi>; evt (\<pi>' ! j) = evt (\<pi> ! j); \<forall>x \<in> set X. st \<pi>' (j - 1) x = st \<pi> (j - 1) x; \<forall>x \<in> set A. st \<pi>' (j - 1) x = None\<rbrakk> \<Longrightarrow> (j, b) \<in> set (monitor_decisions s a c \<pi>')"
  by (rule monitor_evidence_stable)

ML \<open>
  val accepted = [("accept_names", @{thm accept_names}), ("accept_shape", @{thm accept_shape}), ("accept_present_free", @{thm accept_present_free}), ("accept_definite_U", @{thm accept_definite_U}), ("accept_definite", @{thm accept_definite}), ("accept_definite_pf", @{thm accept_definite_pf}), ("accept_completions", @{thm accept_completions}), ("accept_undefined_U", @{thm accept_undefined_U}), ("accept_undefined_absent", @{thm accept_undefined_absent}), ("accept_undefined_stays", @{thm accept_undefined_stays}), ("accept_undefined_resolved", @{thm accept_undefined_resolved}), ("accept_undefined_pf", @{thm accept_undefined_pf}), ("accept_supports_sound", @{thm accept_supports_sound}), ("accept_supports_mono", @{thm accept_supports_mono}), ("accept_supports", @{thm accept_supports}), ("accept_decisions", @{thm accept_decisions}), ("accept_append", @{thm accept_append}), ("accept_stable", @{thm accept_stable})]
  val n = length accepted
  fun consts_of th = Term.add_const_names (Thm.prop_of th) []

  (* (a) Every constant of a lemma is declared in the core (with HOL) or is one of the
     three constants of TRIEL_Evidence_Def. A constant that the stage declares under a
     name of the core is in neither. *)
  val core = @{theory TRIEL_Completions}
  val evid =
    ["TRIEL_Evidence_Def.evidence", "TRIEL_Evidence_Def.supports",
     "TRIEL_Evidence_Def.monitor_evidence"]
  fun allowed c = Sign.declared_const core c orelse member (op =) evid c
  val bad =
    accepted |> maps (fn (_, th) => consts_of th) |> distinct (op =) |> filter_out allowed
  val _ =
    if null bad then ()
    else error ("Accept_Evidence: an accepted lemma uses a constant not of the core or of TRIEL_Evidence_Def: " ^ commas bad)

  (* (b) Each lemma uses the constants it is about. *)
  val required =
    [("accept_names", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.names", "TRIEL_Core.pnames"]),
     ("accept_shape", ["TRIEL_Evidence_Def.evidence"]),
     ("accept_present_free", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.present_free"]),
     ("accept_definite_U", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval"]),
     ("accept_definite", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval"]),
     ("accept_definite_pf", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval", "TRIEL_Core.present_free"]),
     ("accept_completions", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval", "TRIEL_Core.present_free", "TRIEL_Completions.completion"]),
     ("accept_undefined_U", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval"]),
     ("accept_undefined_absent", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval"]),
     ("accept_undefined_stays", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval"]),
     ("accept_undefined_resolved", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval"]),
     ("accept_undefined_pf", ["TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval", "TRIEL_Core.present_free", "TRIEL_Core.info_le"]),
     ("accept_supports_sound", ["TRIEL_Evidence_Def.supports", "TRIEL_Core.eval", "TRIEL_Core.present_free"]),
     ("accept_supports_mono", ["TRIEL_Evidence_Def.supports", "TRIEL_Core.present_free"]),
     ("accept_supports", ["TRIEL_Evidence_Def.supports", "TRIEL_Evidence_Def.evidence", "TRIEL_Core.eval", "TRIEL_Core.present_free"]),
     ("accept_decisions", ["TRIEL_Evidence_Def.monitor_evidence", "TRIEL_Breach.monitor_decisions"]),
     ("accept_append", ["TRIEL_Evidence_Def.monitor_evidence"]),
     ("accept_stable", ["TRIEL_Evidence_Def.monitor_evidence", "TRIEL_Breach.monitor_decisions", "TRIEL_Trace.st", "TRIEL_Trace.evt"])]
  val missing =
    required
    |> maps (fn (name, cs) =>
        let val have = consts_of (the (AList.lookup (op =) accepted name))
        in map (fn c => name ^ ": " ^ c) (filter_out (member (op =) have) cs) end)
  val _ =
    if null missing then ()
    else error ("Accept_Evidence: an accepted lemma lacks a constant it is about: " ^ commas missing)

  (* (c) No accepted lemma depends on an oracle. *)
  val oracles =
    distinct (op =) (map (fn ((name, _), _) => name) (Thm_Deps.all_oracles (map snd accepted)))
  val _ =
    if null oracles then ()
    else error ("Accept_Evidence: an accepted lemma depends on an oracle: " ^ commas oracles)
  val _ = writeln ("Accept_Evidence: " ^ string_of_int n ^ " lemmas, no oracle, constants as required")
\<close>

end
