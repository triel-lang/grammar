(*  Title:      Lex_Evidence.thy
    The lexical check of TRIEL_Evidence.thy. Written by the maintainers, not by the stage;
    the stage may not change this file (its SHA-256 is checked). The ML block reads the
    text of ../TRIEL_Evidence.thy and splits it into tokens with the lexer of Isabelle and
    the keywords that TRIEL_Evidence.thy sees: its header may import only
    TRIEL_Evidence_Def, which imports TRIEL_Core.TRIEL_Completions, as this theory does,
    and declares no keywords. The block fails if the header is not exactly
    "theory TRIEL_Evidence imports TRIEL_Evidence_Def begin" or the file does not end with
    its one end; if a command is not in the list below; if any other token, names, strings,
    cartouches and comments alike, holds a denied word (also inside a word, so that a
    method named in quotes or nested in a cartouche is found), an antiquotation, a control
    symbol or an escaped character; or if there is a lexical error. The session does not
    import TRIEL_Evidence, so no code of the stage runs before or during this check.
*)

theory Lex_Evidence
  imports TRIEL_Core.TRIEL_Completions
begin

ML \<open>
  val file = Path.append (Resources.master_directory @{theory}) (Path.explode "../TRIEL_Evidence.thy")
  val toks = Token.explode (Thy_Header.get_keywords @{theory}) Position.none (File.read file)
  val proper = filter Token.is_proper toks

  (* The commands a theory of lemmas and their proofs needs; every other command (ML and
     its relatives, axiomatization, oracle, sorry, oops, syntax, notation, class, locale,
     context, bundle, instance ...) is refused. *)
  val allowed_commands =
    ["theory", "begin", "end", "section", "subsection", "subsubsection", "paragraph", "text", "txt",
     "lemma", "theorem", "corollary", "proposition", "lemmas", "declare",
     "definition", "fun", "primrec", "function", "termination",
     "proof", "qed", "by", ".", "..", "apply", "done", "subgoal", "defer", "prefer", "supply",
     "using", "unfolding", "have", "show", "hence", "thus", "obtain", "fix", "assume", "presume",
     "case", "next", "then", "from", "with", "note", "moreover", "ultimately", "also", "finally",
     "let", "define", "consider", "{", "}"]

  (* Words that switch off the check of proofs, run ML inside a proof method or set the
     ML environment; refused anywhere in a token, even inside a longer word. *)
  val denied_words = ["quick_and_dirty", "skip_proofs", "tactic", "ML_"]

  (* The backslash is built from its code: written in this text, a backslash before "<^"
     begins an Isabelle symbol for the outer lexer and an escape for the lexer of ML. *)
  val bs = String.str (Char.chr 92)
  fun control_in s =
    exists (fn x => String.isPrefix (bs ^ "<^") x andalso x <> bs ^ "<^sub>" andalso x <> bs ^ "<^sup>")
      (Symbol.explode s)
  fun escape_in s =
    exists (fn (a, b) => a = bs andalso Symbol.is_ascii_digit b)
      (let val xs = Symbol.explode s in if null xs then [] else xs ~~ (tl xs @ [""]) end)
  fun text_problems s =
    map (fn w => "the word " ^ quote w) (filter (fn w => String.isSubstring w s) denied_words)
    @ (if String.isSubstring "@{" s orelse control_in s then ["an antiquotation or control symbol in " ^ quote s] else [])
    @ (if escape_in s then ["an escaped character in " ^ quote s] else [])

  fun problems_of tok =
    if Token.is_command tok then
      if member (op =) allowed_commands (Token.content_of tok) then []
      else ["the command " ^ quote (Token.content_of tok)]
    else
      (case Token.kind_of tok of
        Token.Control _ => ["the control symbol in " ^ quote (Token.source_of tok)]
      | Token.Error msg => ["a lexical error: " ^ msg]
      | _ => distinct (op =) (text_problems (Token.source_of tok) @ text_problems (Token.content_of tok)))

  fun count_command name =
    length (filter (fn t => Token.is_command t andalso Token.content_of t = name) toks)
  val header = map Token.content_of (take 5 proper)
  val shape_ok =
    header = ["theory", "TRIEL_Evidence", "imports", "TRIEL_Evidence_Def", "begin"]
    andalso count_command "theory" = 1 andalso count_command "end" = 1
    andalso (case rev proper of t :: _ => Token.is_command t andalso Token.content_of t = "end" | [] => false)

  val problems =
    (if shape_ok then []
     else ["the header is not \"theory TRIEL_Evidence imports TRIEL_Evidence_Def begin\" or the file does not end with its one end"])
    @ distinct (op =) (maps problems_of toks)
  val _ =
    if null problems then ()
    else error ("Lex_Evidence: TRIEL_Evidence.thy is not accepted: " ^ commas problems)
  val _ =
    writeln ("Lex_Evidence: " ^ string_of_int (length (filter Token.is_command toks)) ^
      " commands, all allowed")
\<close>

end
