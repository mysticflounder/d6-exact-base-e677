---
title: "The $d=6$ Exact-Base Branch for E677 Magmas"
author: Adam McKenna
date: May 2026
abstract: |
  We isolate and formalize a $d=6$ exact-base branch in finite E677 magmas.
  In the branch considered here, a distinguished element $x$ has left orbit
  $c_0 = x,\ c_1 = x \D x,\ c_2 = x \D c_1,\ \ldots,\ c_5 = x \D c_4$,
  together with an outsider element $A$ satisfying the exact-base rows
  $A \D A = c_1$, $A \D x = c_3$, $c_3 \D c_3 = c_1$.
  Under the $d=6$ gap-1 context hypotheses, these rows force
  $c_4 \D x = x$, and therefore $((x \D x) \D x) \D x = x$.
  The Lean formalization exposes this result through
  \texttt{D6ExactBasePacket.fixer} in \texttt{lean/E677/D6Publication.lean}.
  The theorem is independent of the large gap-1 dispatcher and verifies with
  only standard Lean axioms.
header-includes:
  - \usepackage{amsmath,amssymb,amsthm}
  - \usepackage{hyperref}
  - \usepackage{tikz}
  - \usetikzlibrary{arrows.meta}
  - \usepackage{listings}
  - \usepackage{xcolor}
  - \lstdefinelanguage{Lean4}{keywords={theorem,structure,where,def,fun,let,have,by,apply,exact,Type,Prop,Sort,instance,class,extends,open,namespace,end,import,abbrev,deriving},sensitive=true,morecomment=[l]{--},morecomment=[s]{/-}{-/}}
  - \lstset{language=Lean4,basicstyle=\small\ttfamily,keywordstyle=\bfseries,commentstyle=\itshape\color{gray!70},frame=single,rulecolor=\color{gray!40},backgroundcolor=\color{gray!6},xleftmargin=1.5em,xrightmargin=1.5em,breaklines=true,aboveskip=0.9em,belowskip=0.9em}
  - \newcommand{\D}{\mathbin{\diamond}}
  - \newtheorem{theorem}{Theorem}[section]
  - \newtheorem{lemma}[theorem]{Lemma}
  - \newtheorem{corollary}[theorem]{Corollary}
  - \theoremstyle{definition}
  - \newtheorem{definition}[theorem]{Definition}
  - \newtheorem{remark}[theorem]{Remark}
  - \renewcommand{\qedsymbol}{}
---

# Background

An E677 magma is a magma $(M, \D)$ satisfying the identity
$$a = b \D (a \D ((b \D a) \D b))$$
for all $a, b \in M$. We study finite E677 magmas by analyzing
left-orbits under maps of the form $L_x(z) = x \D z$.

For a fixed non-idempotent element $x$, write $c_i = L_x^i(x)$.
The $d=6$ branch is the case where the relevant left orbit has six named elements
$c_0, c_1, c_2, c_3, c_4, c_5$ with $c_0 = x$ and
$$x \D c_i = c_{i+1} \quad \text{for } 0 \le i < 5, \qquad x \D c_5 = x.$$

\begin{figure}[h]
\centering
\begin{tikzpicture}[
  vertex/.style={circle, draw, minimum size=0.8cm, font=\small},
  >=Stealth, semithick
]
\def\R{2.3}
\node[vertex] (c0) at ( 90:\R) {$x$};
\node[vertex] (c1) at ( 30:\R) {$c_1$};
\node[vertex] (c2) at (-30:\R) {$c_2$};
\node[vertex] (c3) at (-90:\R) {$c_3$};
\node[vertex] (c4) at (210:\R) {$c_4$};
\node[vertex] (c5) at (150:\R) {$c_5$};
\draw[->] (c0) -- (c1);
\draw[->] (c1) -- (c2);
\draw[->] (c2) -- (c3);
\draw[->] (c3) -- (c4);
\draw[->] (c4) -- (c5);
\draw[->] (c5) -- (c0);
\draw[->, dashed] (c4) -- node[pos=0.52, above right, font=\footnotesize]
  {$c_4 \D x = x$} (c0);
\end{tikzpicture}
\caption{The $d=6$ orbit of $x$ under $L_x$. Solid arrows show
$x \D c_i = c_{i+1}$ (with $c_0 = x$) and $x \D c_5 = x$.
The dashed arrow is the main conclusion of Theorem~\ref{thm:main}.}
\label{fig:orbit}
\end{figure}

The formal Lean context packages the branch as \texttt{D6Gap1Context}.
This context records the E677 law, the six orbit elements, an outsider $A$,
the $d=6$ orbit rows, and the auxiliary gap-1 rows needed by the isolated proof.

## The exact-base branch

The larger classifier enumerates all possible behaviors of an outsider element
$A \notin \{c_0,\ldots,c_5\}$ under the $d=6$ gap-1 constraints.
The exact-base branch is distinguished by three conditions: $A \D A$ lands at $c_1$ (the first non-trivial orbit element),
$A \D x$ lands at $c_3$ (the exact midpoint of the orbit, hence ``exact
base''), and $c_3 \D c_3 = c_1$. The last condition is not independent: the
gap-1 classifier shows it is forced once the first two hold. Together they
constitute the minimal set of rows needed to close the $c_4 \D x = x$ derivation.

# Exact-Base Packet

The exact-base branch adds three rows to the $d=6$ context:
$$A \D A = c_1, \qquad A \D x = c_3, \qquad c_3 \D c_3 = c_1.$$

In Lean these rows are packaged as, together with the two publication-facing theorems:

\begin{lstlisting}
structure D6ExactBasePacket (alpha : Type u) [Magma' alpha] [Fintype alpha] where
  ctx : D6Gap1Context alpha
  hAA : ctx.A * ctx.A = ctx.c1
  hA0 : ctx.A * ctx.x = ctx.c3
  hT1 : ctx.c3 * ctx.c3 = ctx.c1

theorem D6ExactBasePacket.fixer (P : D6ExactBasePacket alpha) :
    (((P.ctx.x * P.ctx.x) * P.ctx.x) * P.ctx.x) = P.ctx.x

theorem D6ExactBasePacket.c4_mul_x_eq_x (P : D6ExactBasePacket alpha) :
    P.ctx.c4 * P.ctx.x = P.ctx.x
\end{lstlisting}

# Main Theorem

\begin{theorem}\label{thm:main}
Let $M$ be a finite E677 magma, and let $x$ be an element in a $d=6$ gap-1
context with orbit elements $c_0 = x, c_1, c_2, c_3, c_4, c_5$.
Suppose there is an outsider $A$ satisfying the exact-base rows
\[A \D A = c_1, \qquad A \D x = c_3, \qquad c_3 \D c_3 = c_1.\]
Then
\[((x \D x) \D x) \D x = x.\]
Equivalently, the fourth left iterate of $x$ under $L_x$ returns to $x$.
\end{theorem}

# Proof

The central objective is to establish $c_4 \D x = x$.
Once this row is known, the conclusion of Theorem \ref{thm:main} follows
immediately because
$$((x \D x) \D x) \D x = c_4 \D x = x.$$

The proof proceeds through three lemmas.

\begin{lemma}[{\texttt{exact\_packet\_c3\_mul\_c1\_eq\_x}}]\label{lem:c3c1}
$c_3 \D c_1 = x$.
\end{lemma}

\begin{proof}
From $A \D x = c_3$ and the gap-1 context row $A \D (A \D x) = A$,
substituting gives $A \D c_3 = A$.
Applying the E677 law with $b = A$, $a = c_3$:
\begin{align*}
c_3 &= A \D \bigl(c_3 \D ((A \D c_3) \D A)\bigr) \\
    &= A \D \bigl(c_3 \D (A \D A)\bigr)
       && \text{(since $A \D c_3 = A$)} \\
    &= A \D (c_3 \D c_1).
       && \text{(exact-base: $A \D A = c_1$)}
\end{align*}
Since $A \D x = c_3$ as well, left cancellation by $A$ gives $c_3 \D c_1 = x$.
\end{proof}

\begin{lemma}[{\texttt{exact\_packet\_c1\_mul\_c4\_eq\_c3}}]\label{lem:c1c4}
$c_1 \D c_4 = c_3$.
\end{lemma}

\begin{proof}
Applying the E677 law with $b = c_3$, $a = c_1$:
\begin{align*}
c_1 &= c_3 \D \bigl(c_1 \D ((c_3 \D c_1) \D c_3)\bigr) \\
    &= c_3 \D \bigl(c_1 \D (x \D c_3)\bigr)
       && \text{(Lemma~\ref{lem:c3c1}: $c_3 \D c_1 = x$)} \\
    &= c_3 \D (c_1 \D c_4).
       && \text{(orbit: $x \D c_3 = c_4$)}
\end{align*}
Since $c_3 \D c_3 = c_1$ (exact-base row), left cancellation by $c_3$ gives
$c_1 \D c_4 = c_3$.
\end{proof}

\begin{lemma}[{\texttt{exact\_packet\_c4\_mul\_x\_eq\_x}}]\label{lem:c4x}
$c_4 \D x = x$.
\end{lemma}

\begin{proof}
Applying the E677 law with $b = c_1$, $a = c_4$:
\begin{align*}
c_4 &= c_1 \D \bigl(c_4 \D ((c_1 \D c_4) \D c_1)\bigr) \\
    &= c_1 \D \bigl(c_4 \D (c_3 \D c_1)\bigr)
       && \text{(Lemma~\ref{lem:c1c4}: $c_1 \D c_4 = c_3$)} \\
    &= c_1 \D (c_4 \D x).
       && \text{(Lemma~\ref{lem:c3c1}: $c_3 \D c_1 = x$)}
\end{align*}
The $d=6$ context gives $c_1 \D x = c_4$; left cancellation by $c_1$ gives
$c_4 \D x = x$.
\end{proof}

The orbit definition gives $c_4 = ((x \D x) \D x) \D x$, so
Lemma \ref{lem:c4x} completes the proof of Theorem \ref{thm:main}.
The corresponding Lean names are \texttt{D6Gap1Context.fixer\_of\_exact\_packet}
and \texttt{D6ExactBasePacket.fixer}.

# Formalization Status

The Lean source and paper are available at
\url{https://github.com/mysticflounder/d6-exact-base-e677}.

The standalone publication surface is \texttt{lean/E677/D6Publication.lean},
which imports only \texttt{E677.D6Isolated}. The isolated proof file
\texttt{lean/E677/D6Isolated.lean} imports only \texttt{E677.D6CoreMinimal},
which in turn imports only \texttt{E677.Basic}.

We validated the build with \texttt{lake build E677.D6Publication E677.D6TransportPacket E677.D6Full}.
Running \texttt{lean\_verify} on \texttt{D6ExactBasePacket.fixer}
confirms its axiom footprint is \texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}.
The publication theorem does not depend on the remaining
project \texttt{sorry} declarations in \texttt{Core.lean} or \texttt{Gap1.lean}.

# Acknowledgments

The author acknowledges use of Claude (Anthropic) and Codex/ChatGPT (OpenAI)
for proof brainstorming, SAT/DRAT encodings, and code generation for both the
Lean proofs and supporting tools.

# Minimal Extraction Slice\label{sec:slice}

The minimal Lean slice for extraction comprises
\texttt{lean/E677/Basic.lean},
\texttt{lean/E677/D6CoreMinimal.lean},
\texttt{lean/E677/D6Isolated.lean}, and
\texttt{lean/E677/D6Publication.lean}.
The large gap-1 dispatcher remains useful for the full project but is not
part of the $d=6$ exact-base proof body.
