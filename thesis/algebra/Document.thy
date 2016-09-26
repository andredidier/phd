(*<*)
theory Document
imports Temporal_Faults_Algebra_dlist 
  "~~/src/HOL/Library/LaTeXsugar"
  "~~/src/HOL/Library/OptionalSugar"
begin
(*>*)

(*<*)
notation (output)
  dlist_xbefore ("_\<rightarrow>_(_)" [80,80,80] 80) and
  xbefore ("_\<rightarrow>_" [80,80] 80) and
  tempo1 ("vremya\<^sub>1 _" 80) and
  tempo2 ("vremya\<^sub>2 _" 80) and
  tempo3 ("vremya\<^sub>3 _" 80) and
  slice ("(3_\<^bsub>[_.._]\<^esub>)"  [80,80,80] 80) and
  slice_left ("(2_\<^bsub>[_..]\<^esub>)" [80,80] 80) and
  slice_right ("(2_\<^bsub>[.._]\<^esub>)" [80,80] 80) and 
  Abs_formula ("") and
  Rep_formula ("")
(*>*)

text {*
\begin{definition}{XBefore}
@{thm [display] xbefore_formula_def}
\end{definition}
*}

text {*
\begin{definition}[Distinct]
A list @{term "xs"} is @{term "distinct"} if it has no repeated element. 
\end{definition}

So, if @{term "x"} is in @{term "xs"}, then it has a unique associated index @{term "i"} and we 
denote it as @{term "nth xs i"}.

The set of sets of distinct lists form a free algebra, similarly to \acp{FBA}. \emph{Infimum} and 
\emph{Supremum} are defined as set intersection (@{text "$\<inter>$"}) and union (@{text "$\<union>$"}) respectively. 
The order of the algebra's lattice is defined with set inclusion (@{text "$\<subseteq>,\<subset>$"}).

From a set of @{term "n"} free variables there are @{term "fact n"} lists and we need an operator
to distinguish all these @{term "fact n"} to build the algebra. We define this operator as the
\ac{XBefore} in terms of list appending, as is is in~\cite{DM2015}.
*}
(*
\begin{definition}[XBefore with appending]
\label{def:xbefore-append}
Given two sets of distinct lists @{text "A"} and @{text "B"}, the XBefore operator with appending
is:                                 
@{thm [display] dlistset_xbefore_append_def[no_vars] }
\end{definition}*)
text {*
An equivalent definition is given in terms of lists slicing using indexes~\cref{def:xbefore}. 
In some cases it is more intuitive to use~\cref{def:xbefore}, so \cref{thm:xbefore-append-slice} 
shows that the two definitions are equivalent.
Lists slicing is the operation of taking or droping elements, obtaining a sublist. 
The starting index is inclusive, and the ending is exclusive, thus the first index is 0 and the 
last index is the size of the list. For example, the list @{term "xs\<dagger>0..(Dlist.length xs)"} is equal 
to the @{text "xs"}.

\begin{definition}[XBefore]
\label{def:theory-xbefore}
Given two sets of distinct lists @{text "A"} and @{text "B"}, the XBefore operator with slicing
is:
@{term [display] "xbefore a b" } = @{term [display] "Collect (dlist_xbefore a b)"}
\end{definition}

\begin{lemma}[XBefore with appending is equivalent to XBefore with slicing]
\label{thm:theory-xbefore-append-slice}
Given two sets of distinct lists @{text "A"} and @{text "B"}, the XBefore definition is append
is equivalent to the definition with slicing:
@{thm (rhs) dlist_xbefore_append} @{text "\<equiv>"} @{thm (rhs) dlist_xbefore_def}
\end{lemma}
\begin{proof}
The proof follows directly the property that 
@{term "list_of_dlist (xs\<dagger>..i) @ list_of_dlist (xs\<dagger>i..) = list_of_dlist xs"}.
\end{proof}

The XBefore has some properties that follows from its definition.

\begin{lemma}[XBefore is not symmetric]
\label{thm:theory-xbefore-not-sym}
Given two sets of distinct lists, @{thm (prem 1) dlist_xbefore_and} and 
@{thm (prem 2) dlist_xbefore_and}, then
@{thm [display] (concl) dlist_xbefore_and}
\end{lemma}


*}

(*<*)
end
(*>*)