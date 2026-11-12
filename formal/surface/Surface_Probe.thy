(*  Title:      Surface_Probe.thy
    Purpose:    A probe: a parse tree of parser/triel.lark with the texts of its tokens, texts
                outside ASCII among them, through functions of HOL and the exported Haskell
                code to an atom of the core. The theories of formal/core are imported, not
                changed.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory Surface_Probe
  imports TRIEL_Core.TRIEL_Exec
begin

section \<open>Parse trees\<close>

text \<open>A parse tree of parser/triel.lark: a node is the name of a rule with the list of its
  children, a leaf is the name of a terminal with the text of its token, and an absent
  optional element is a constructor of its own. The text is a type parameter: a
  String.literal in the first variant, the list of the codes of its characters in the
  second.\<close>

datatype 't ptree = Node String.literal "'t ptree list" | Leaf String.literal 't | Absent

type_synonym lit_tree = "String.literal ptree"
type_synonym codes_tree = "integer list ptree"

text \<open>The texts of the leaves of the terminal STRING_LITERAL, in preorder.\<close>

fun str_leaves :: "'t ptree \<Rightarrow> 't list" where
  "str_leaves (Node r cs) = concat (map str_leaves cs)"
| "str_leaves (Leaf n x) = (if n = STR ''STRING_LITERAL'' then [x] else [])"
| "str_leaves Absent = []"


section \<open>Four functions over the texts of STRING_LITERAL\<close>

text \<open>For each variant: (a) the texts as they are; (b) whether each text is the ASCII
  constant \<open>"delivered"\<close> (with the quotes, as in the token); (c) the codes of the characters
  of each text; (d) the atom \<open>AStr\<close> of the core for each text. In the first variant (c) is
  \<open>String.asciis_of_literal\<close> and (d) is \<open>AStr\<close> of the text as it is; in the second (c) is
  the identity and (d) goes through \<open>String.literal_of_asciis\<close>, the only way from codes to
  a String.literal.\<close>

definition str_const :: String.literal where
  \<open>str_const = STR ''"delivered"''\<close>

definition str_const_codes :: "integer list" where
  "str_const_codes = [34, 100, 101, 108, 105, 118, 101, 114, 101, 100, 34]"

subsection \<open>First variant: the text is a String.literal\<close>

definition lit_texts :: "lit_tree \<Rightarrow> String.literal list" where
  "lit_texts t = str_leaves t"

definition lit_eq :: "lit_tree \<Rightarrow> bool list" where
  "lit_eq t = map (\<lambda>x. x = str_const) (str_leaves t)"

definition lit_codes :: "lit_tree \<Rightarrow> integer list list" where
  "lit_codes t = map String.asciis_of_literal (str_leaves t)"

definition lit_atoms :: "lit_tree \<Rightarrow> atom list" where
  "lit_atoms t = map AStr (str_leaves t)"

subsection \<open>Second variant: the text is the list of the codes of its characters\<close>

definition codes_texts :: "codes_tree \<Rightarrow> integer list list" where
  "codes_texts t = str_leaves t"

definition codes_eq :: "codes_tree \<Rightarrow> bool list" where
  "codes_eq t = map (\<lambda>x. x = str_const_codes) (str_leaves t)"

definition codes_codes :: "codes_tree \<Rightarrow> integer list list" where
  "codes_codes t = map id (str_leaves t)"

definition codes_atoms :: "codes_tree \<Rightarrow> atom list" where
  "codes_atoms t = map (\<lambda>x. AStr (String.literal_of_asciis x)) (str_leaves t)"


section \<open>Two functions without a case for an absent element\<close>

text \<open>Both give the name of a node or of a leaf. \<open>name_fun\<close> is defined by \<open>fun\<close> without an
  equation for \<open>Absent\<close>, \<open>name_case\<close> by \<open>case\<close> without a branch for \<open>Absent\<close>.\<close>

fun name_fun :: "'t ptree \<Rightarrow> String.literal" where
  "name_fun (Node r cs) = r"
| "name_fun (Leaf n x) = n"

definition name_case :: "'t ptree \<Rightarrow> String.literal" where
  "name_case t = (case t of Node r cs \<Rightarrow> r | Leaf n x \<Rightarrow> n)"


section \<open>Export\<close>

text \<open>One export with the evaluator \<open>run\<close> and the constructors of \<open>atom\<close>, as for a
  translation of parse trees into terms of the core. The two ML commands write the time of
  the export as a message of the theory.\<close>

ML \<open>val probe_export_start = Timing.start ()\<close>

export_code run ABool ANum AStr ATime Node Leaf Absent
  lit_texts lit_eq lit_codes lit_atoms codes_texts codes_eq codes_codes codes_atoms
  name_fun name_case
  in Haskell module_name TRIEL_Surface_Probe

ML \<open>writeln ("probe timing: export_code " ^ Timing.message (Timing.result probe_export_start))\<close>

end
