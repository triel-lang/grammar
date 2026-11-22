(*  Title:      Accept_MFOTL1.thy
    Acceptance of part 1 of the bridge from the TRIEL core to MFOTL. Written by the
    maintainers, not by the stage; the stage may not change this file (its SHA-256 is
    checked in CI). Each lemma restates a theorem of the session TRIEL_MFOTL exactly and
    proves it by that theorem alone. Every type variable carries its sort, so a bridge
    whose constants need a narrower type or a further class does not parse here. The ML block at the end fails if a lemma uses a
    constant that is neither of the core, of the AFP entry MFOTL_Checker (with HOL) nor
    one of the nine constants of the bridge named below; if a lemma does not use the
    constants of the core it is about; or if a lemma depends on an oracle (an unfinished
    proof is one). The satisfaction relation is written Formula.sat, without notation:
    the AFP switches its notation off at the end of the theory Formula.
*)

theory Accept_MFOTL1
  imports TRIEL_Core.TRIEL_Breach TRIEL_MFOTL.TRIEL_MFOTL_Cond
begin

text \<open>The encoding is exactly the one of the evaluation of the bridge (3.1).\<close>

lemma accept_db:
  "enc_db C (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace) j =
     {(''val'', [MN x, MV u]) | x u. st \<pi> j x = Some u}
   \<union> {(''lt'', [MV u, MV w]) | u w. u \<in> ran (st \<pi> j) \<union> C \<and> w \<in> ran (st \<pi> j) \<union> C \<and> vless u w}
   \<union> {(''le'', [MV u, MV w]) | u w. u \<in> ran (st \<pi> j) \<union> C \<and> w \<in> ran (st \<pi> j) \<union> C \<and> vleq u w}
   \<union> (case evt (\<pi> ! j) of
        Arrival x \<Rightarrow> {(''arr'', [MN x])}
      | Deontic s a p \<Rightarrow> (if j = 0 then {} else {(''act'', [MS s, MA a])})
      | Tick \<Rightarrow> {})"
  by (rule enc_db_eq)

lemma accept_pre:
  "enc_pre C (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace) (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace) \<longleftrightarrow>
     (\<forall>j < length \<pi>. \<Gamma> \<sigma> j = enc_db C \<pi> j \<and> \<tau> \<sigma> j = nat (time \<pi> j - time \<pi> 0))"
  by (rule enc_pre_iff)

text \<open>The encoding gives every entry of a trace a finite database, so a trace of MFOTL
  with the encoded prefix exists; the constants of a condition are finitely many.\<close>

lemma accept_exists:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); finite C; \<forall>j < length \<pi>. finite (dom (st \<pi> j))\<rbrakk>
   \<Longrightarrow> \<exists>\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace. enc_pre C \<pi> \<sigma>"
  by (rule enc_pre_exists)

lemma accept_econsts: "finite (econsts (c :: ('n :: type, 'v :: value_order) TRIEL_Core.expr))"
  by (rule econsts_finite)

text \<open>Time: the timestamp of MFOTL is the time of the entry, counted from the first.\<close>

lemma accept_time:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> int (\<tau> \<sigma> j) = time \<pi> j - time \<pi> 0"
  by (rule enc_time)

text \<open>Order: the facts lt and le of the database are exactly vless and vleq on the
  values of the state and the constants of C.\<close>

lemma accept_lt:
  "\<lbrakk>u \<in> ran (st (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace) j) \<union> C; w \<in> ran (st \<pi> j) \<union> C\<rbrakk>
   \<Longrightarrow> ((''lt'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vless u w)"
  by (rule enc_db_lt)

lemma accept_le:
  "\<lbrakk>u \<in> ran (st (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace) j) \<union> C; w \<in> ran (st \<pi> j) \<union> C\<rbrakk>
   \<Longrightarrow> ((''le'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vleq u w)"
  by (rule enc_db_le)

text \<open>The three-valued condition is a pair of formulas, with no premise on the
  completeness of the data.\<close>

lemma accept_true:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> eval c (st \<pi> j) = Some True \<longleftrightarrow> Formula.sat \<sigma> v j (Pc c)"
  by (rule bridge_true)

lemma accept_false:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> eval c (st \<pi> j) = Some False \<longleftrightarrow> Formula.sat \<sigma> v j (Nc c)"
  by (rule bridge_false)

lemma accept_blocks:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> blocks c (st \<pi> j) \<longleftrightarrow> \<not> Formula.sat \<sigma> v j (Nc c)"
  by (rule bridge_blocks_cond)

text \<open>With complete data (the names of the core's theorem T4) the condition is defined
  and equals the truth of Pc.\<close>

lemma accept_complete:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C; names c \<subseteq> dom (st \<pi> j)\<rbrakk>
   \<Longrightarrow> eval c (st \<pi> j) = Some (Formula.sat \<sigma> v j (Pc c))"
  by (rule bridge_complete_cond)

ML \<open>
  val accepted =
    [("accept_db", @{thm accept_db}), ("accept_pre", @{thm accept_pre}),
     ("accept_exists", @{thm accept_exists}), ("accept_econsts", @{thm accept_econsts}),
     ("accept_time", @{thm accept_time}), ("accept_lt", @{thm accept_lt}),
     ("accept_le", @{thm accept_le}), ("accept_true", @{thm accept_true}),
     ("accept_false", @{thm accept_false}), ("accept_blocks", @{thm accept_blocks}),
     ("accept_complete", @{thm accept_complete})]
  val n = length accepted
  fun consts_of th = Term.add_const_names (Thm.prop_of th) []

  (* (a) Every constant of a lemma is declared in the core (with HOL), in the AFP theory
     Formula (with its ancestors), or is one of the nine constants of the bridge. A
     constant that the bridge declares under a name of the core (eval, blocks, st, ran, ...)
     is in none of the three. An abbreviation is unfolded before this check, so the
     theories of the bridge may not declare one (step (2) of mfotl.yml). *)
  val core = @{theory TRIEL_Breach}
  val afp = @{theory Formula}
  val bridge =
    ["TRIEL_MFOTL_Enc.enc_db", "TRIEL_MFOTL_Enc.enc_pre",
     "TRIEL_MFOTL_Enc.mval.MN", "TRIEL_MFOTL_Enc.mval.MV",
     "TRIEL_MFOTL_Enc.mval.MS", "TRIEL_MFOTL_Enc.mval.MA",
     "TRIEL_MFOTL_Cond.econsts", "TRIEL_MFOTL_Cond.Pc", "TRIEL_MFOTL_Cond.Nc"]
  fun allowed c =
    Sign.declared_const core c orelse Sign.declared_const afp c orelse member (op =) bridge c
  val bad =
    accepted
    |> maps (fn (_, th) => consts_of th)
    |> distinct (op =)
    |> filter_out allowed
  val _ =
    if null bad then ()
    else error ("Accept_MFOTL1: an accepted lemma uses a constant not of the core, of Formula or of the bridge: " ^ commas bad)

  (* (b) Each lemma uses the constants of the core and the AFP it is about. *)
  val required =
    [("accept_db", ["TRIEL_MFOTL_Enc.enc_db", "TRIEL_Trace.st", "TRIEL_Trace.evt",
        "TRIEL_Core.value_order_class.vless", "TRIEL_Core.value_order_class.vleq"]),
     ("accept_pre", ["TRIEL_MFOTL_Enc.enc_pre", "TRIEL_MFOTL_Enc.enc_db", "Trace.\<Gamma>",
        "Trace.\<tau>", "TRIEL_Breach.time"]),
     ("accept_exists", ["TRIEL_MFOTL_Enc.enc_pre", "TRIEL_Trace.is_trace", "TRIEL_Trace.st"]),
     ("accept_econsts", ["TRIEL_MFOTL_Cond.econsts"]),
     ("accept_time", ["TRIEL_MFOTL_Enc.enc_pre", "TRIEL_Trace.is_trace", "Trace.\<tau>",
        "TRIEL_Breach.time"]),
     ("accept_lt", ["TRIEL_MFOTL_Enc.enc_db", "TRIEL_Trace.st",
        "TRIEL_Core.value_order_class.vless"]),
     ("accept_le", ["TRIEL_MFOTL_Enc.enc_db", "TRIEL_Trace.st",
        "TRIEL_Core.value_order_class.vleq"]),
     ("accept_true", ["TRIEL_Core.eval", "TRIEL_Trace.st", "Formula.sat",
        "TRIEL_MFOTL_Cond.Pc", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_false", ["TRIEL_Core.eval", "TRIEL_Trace.st", "Formula.sat",
        "TRIEL_MFOTL_Cond.Nc", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_blocks", ["TRIEL_Breach.blocks", "TRIEL_Trace.st", "Formula.sat",
        "TRIEL_MFOTL_Cond.Nc", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_complete", ["TRIEL_Core.eval", "TRIEL_Core.names", "TRIEL_Trace.st",
        "Formula.sat", "TRIEL_MFOTL_Cond.Pc"])]
  val missing =
    required
    |> maps (fn (name, cs) =>
        let val have = consts_of (the (AList.lookup (op =) accepted name))
        in map (fn c => name ^ ": " ^ c) (filter_out (member (op =) have) cs) end)
  val _ =
    if null missing then ()
    else error ("Accept_MFOTL1: an accepted lemma lacks a constant it is about: " ^ commas missing)
  val _ = writeln ("Accept_MFOTL1: constants as required in " ^ string_of_int n ^ " lemmas")

  (* (c) No accepted lemma depends on an oracle. *)
  val oracles =
    distinct (op =) (map (fn ((name, _), _) => name) (Thm_Deps.all_oracles (map snd accepted)))
  val _ =
    if null oracles then ()
    else error ("Accept_MFOTL1: an accepted lemma depends on an oracle: " ^ commas oracles)
  val _ = writeln ("Accept_MFOTL1: " ^ string_of_int n ^ " lemmas, no oracle, constants as required")
\<close>

end
