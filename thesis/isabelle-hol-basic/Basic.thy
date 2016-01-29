(*<*)
theory Basic
imports Main 
begin
(*>*)

text {*
From the site\footnote{Accessed 27/jan/2016: \url{https://isabelle.in.tum.de/overview.html}} of the 
creators:
%
\begin{quote}
Isabelle is a generic proof assistant. It allows mathematical formulas to be expressed in a formal 
language and provides tools for proving those formulas in a logical calculus. 
%
The main application 
is the formalization of mathematical proofs and in particular formal verification, which includes 
proving the correctness of computer hardware or software and proving properties of computer 
languages and protocols.
\end{quote}
*}

text {*
Isabelle/HOL\index{Isabelle/HOL} is the most widespread instance of Isabelle. 
\acs{HOL} stands for \acl{HOL}.
%
Isabelle/HOL provides a \ac{HOL} proving environment ready to use, which include: (co)datatypes, 
inductive definitions, recursive functions, locales, custom syntax definition, etc.
%
Proofs can be written in both human\footnote{By human we mean that anyone with mathematics and logic 
basic knowledge---it means that deep programming knowledge is not essential.} and machine-readable 
language based in \ac{Isar}.
%
The tool also includes the \emph{sledgehammer}, a port to call external first-order provers to find
proofs automatically.
%
The user interface is based in jEdit\footnote{Accessed 27/jan/2016: \url{http://www.jedit.org/}}, 
which provides a text editor, syntax parser, shortcuts, etc (see \cref{fig:basic-symmetry-isabelle-window}).

\begin{figure}[t]
  \centering
  \includegraphicsaspectratio[0.8]{basic-symmetry-isabelle-window}
  \caption{Isabelle/HOL window, showing the basic symmetry theorem}
  \label{fig:basic-symmetry-isabelle-window}
\end{figure}

Theories in Isabelle/HOL are based in a few axioms.
%
Isabelle/HOL Library's theories---that comes with the installer---and user's theories are based on 
these axioms.
%
This design decision avoids inconsistencies and paradoxes.

Besides the provided theories, its active community provides a comprehensive \ac{AFP}.
%
Each entry in this archive can be cited and usually contains an \emph{abstract}, a document, and a 
theory file.
%
For example, \iacl{FBA} theory is available in~\cite{Huffm2010}.
%
To use it, it is enough to download and put on the same directory of your own theory files.

Bellow we show an example and explain the overall syntax of the human and machine-readable language.
*}

theorem basic_symmetry:
  assumes "x = y" -- "Assumptions"
  shows "y = x" -- "Hypothesis"
proof - 
text_raw{* \newcommand{\bsproof}{%*}
  have "x = x" .. -- "Proof step"
  from assms -- "Using assumptions" 
    show "y = x" .. -- "Show thesis"
text_raw{* }\\\bsproof\\*}
qed

text {*
Finally, Isabelle/HOL provides \LaTeX{} syntax sugar and allow easy document preparation: this 
entire section was written in a theory file mixing Isabelle's and \LaTeX{}'s syntax).
%
The above theorem can be written using Isabelle's quotation and anti-quotations.
%
For example, we can write it using usual \LaTeX{} theorem environment:
%
\begin{Theo}[Basic symmetry]
Assuming @{thm (prem 1) basic_symmetry}, thus:

\begin{center}
@{thm (concl) basic_symmetry}
\end{center}
\end{Theo}
%
\begin{proof}
\bsproof
\end{proof}

Otherwise specified, in the next sections we will omit proofs because they are all verified using
Isabelle/HOL. 
The complete listing is in \cref{app:formal-proofs-isabelle-hol}.
*}

(*<*)
end
(*>*)