---
cssclasses:
  - academic
  - twocolumn
---

>[!n] Notation
>A set is a "collection of elements"
>We write $x\in A$ if $x$ is an element of A. Otherwise, we write $x\notin A$
>Given two sets $A$ and $B$, $A$ is said to be a subset of B, $A\subseteq B$, $\iff$ $B$ contains all elements of $A$.
> $A\subseteq B \iff A\subseteq B$ and $B\subseteq A$

>[!n] Notation
>$\emptyset$ denotes the set containing no elements $\rightarrow$ empty set

>[!r] Remark
>Given a set A
>$\emptyset\subset A$

>[!def] Definition
>Given a set A, the power set $\mathcal{P}(A)$ is the set of all subsets of $A$
>i.e. $B\in \mathcal{P}(A)\iff B \subseteq A$
>>[!ex] $A=\{a,b\}$
>>$\mathcal{P}(A)=\{\emptyset, \{a\}, \{b\}, \{a,b\}\}$


### Operations on Sets
>[!def] Definition
Given the sets A and B:
The union $A\cup B$ is the set of all elements that are in A or in B
$$A\cup B = \{x: x\in A \ or \ x\in B\}$$
The intersection $A\cap B$ is the set of all elements that are in A and in B
$$A\cap B = \{x: x\in A \ and \ x\in B\}$$
The relative component of A w.r.t.:
B is the set of all elements in B that are not in A
$$B\diagdown A = \{x: x\in B \ and \ x \notin A\}$$
"Sometimes" A and B are sets in a universe X.
$$A^c = X\diagdown A$$
>>[!ex] $A = \{a,b\}, \ B=\{b,c\}$
>>$$A\cup B = \{a,b,c\}$$
>>$$A\cap B = \{b\}$$
>>$$A\diagdown B = \{a\}$$
>>$$B\diagdown A = \{c\}$$

>[!r] Remark
>$A\subseteq {A\cup B}$, $B\subseteq {A\cup B}$
>Proof:
>$x \in A \Rightarrow x\in A \ or \  x \in B \Rightarrow x\in A\cup B$
>
>$A\cap B \subseteq A$, $A\cap B\subseteq B$
>Proof:
>$x \in A\cap B \Rightarrow x\in A \ and \ x\in B \Rightarrow x\in A$

### Law: Demorgan's Law

>[!def] Demorgan's Law
>$$i. (A\cup B)^c = A^c \cap B^c$$
>$$ii. (A\cap B)^c = A^c \cup B^c$$
>>[!pf] of i)
>>$x\in (A\cup B)^c$
>>$$
>\begin{flalign}
>&\iff x\notin A\cup B\\
>&\iff x\notin A \ and \ x\notin B\\
>&\iff x\in A^c \ and \ x\in B^c\\
>&\iff x\in A^c \cap B^c\\
>\end{flalign}
>>$$


### Distributivity

>[!def] Distributivity
>$i) \ A\cup (B\cap C) = (A\cup B) \cap (A\cup C)$
>$ii) \ A\cap (B\cup C) = (A\cap B) \cup (A\cap C)$
>
>>[!pf] of i)
>>$$
>\begin{align}
>x\in A \cup (B\cap C)\\
>&\iff x\in A \ or \ x\in B\cap C\\
>&\iff x\in A \ or \ x\in B \ and \ x\in C\\
>&\iff x\in A \ or \ x\in B \ and \ x\in A \ or \ x\in C\\
>&\iff x\in A\cup B \ and \ x\in A\cup C\\
>&\iff x \in (A\cup B) \cap (A\cup C)\\
>\end{align}
>>$$

>[!def] Given two sets A and B
>$$A \times B = \{(x,y): x\in A, y\in B\}$$
>
>Ex: 
>$$
>\begin{align}
>&A = \{a,b\}, b=\{/\}\\
>&A\times B = \{(a,/), (b,/)\}\\
>&B\times A = \{(/, a), (/, b)\}\\
>\end{align}
>$$

### Relations and Functions

>[!def] Given two sets A and B, a relation R is a subset of $A\times B$
>
>Ex: 
>$$
>
>\begin{align}
>A = \{a,b\}, B=\{b,c\}\\
>(Relations \ from \ A  \to \ B)\\
>&R_1 = \{(a,b), (a,c)\}\\
>&R_2 = \{(b,b)\}\\
>&R_3 = \{(a,b), (a,c), (b,c)\}\\
>\end{align}
>$$
>

>[!def] A function $f$ from $A \text{ to } B \ f:A\rightarrow B$
>is a relation from $A$ to $B$ s.t. for every $a\in A$ there exists a unique $b\in B$ s.t. $(a,b)\in f$
>
>In this course we write $$b=f(a)$$
>
>>[!ex] $A=\{a,b,c\}$$\qquad B=\{1,2,3,4\}$
>>$$
\begin{align*}
R_1 &=\{(a,1), (b,1), (c,2)\}\quad \text{function}\\
R_2 &=\{(a,3), (b,1)\}\quad \text{not a function from }A\to B\\
R_3 &=\{(a,1), (b,1), (c,2), (a,3)\}\quad \text{not a function since $a$ is related}\\ & \qquad \text{ to 2 elements, since $(a,1),(a,3)\in R_{3}$}\\
\end{align*}
>>$$

>[!def] Given a function: $f: A\rightarrow B$
>i) Image set: for $E\subseteq A$
>
>$\qquad$$f(E) = \{y\in B\ :\ y=f(a)\}$ for some $a\in E\}$
>
>ii) Pre-image set: for $H\subseteq B$
>$\qquad f^{-1}(H) = \{x\in A\ :\ f(x)\in H\}$


>[!r] Observation: $f: A\rightarrow B$
>1) If $E\subseteq F\subseteq A$ then $f(E)\subseteq f(F)$
>2) If $H\subseteq K(\subseteq B)$ then $f^{-1}(H)\subseteq f^{-1}(K)$
>
>>[!pf] Proof
>>1) $y\in f(E)\Rightarrow y=f(x)$ for some $x\in E$
>>since $E\subseteq F\ then\ x\in F$
>>$(\Rightarrow y=f(x)$ with $x\in F$)
>>$\Rightarrow y\in f(F)$
>>
>>2) $x\in f^{-1}(H) \Rightarrow f(x)\in H$
>>since $H\subseteq K$ then $f(x)\in k\Rightarrow x\in f^{-1}(K)$
>
>
>>[!ex] Ex: A={$\alpha, \beta, \gamma$} B={a, b, c}
>>
>>$$
>>\begin{align}
>>&f(\alpha) = a, f(\beta)=b, f(\gamma)=a\\
>>&f^{-1}(f(\{\alpha\}))=f^{-1}(\{a\})=\{\alpha, \gamma\}\\
>>\\\\
>>&f(f^{-1}(\{b,c\}))=f(\{\beta\}) = \{b\}
>>\end{align}
>>$$
>[not injective nor subjective]

>[!r] Proposition
>$$
\begin{align}
f: A\rightarrow B \ function\\
&1) \forall\ E\subseteq A \ we \ have \ E\subseteq f^{-1}(f(E))\\
&2) \forall \ H\subseteq B \ we \ have \ f(f^{-1}(H)) \subseteq H
\end{align}
>$$
>
>>[!pf] Proof
>>1. Let $x \in E$ then $f(x)\in f(E)$ then $x\in f^{-1}(f(E))$
>>2. Let $y\in f(f^{-1}(H))$ then $y=f(x)$ for some $x\in f^{-1}(H)$
	>but $x\in f^{-1}(H)$ implies $f(x)[=y]\in H$

>[!def] Given a function $f: A\rightarrow B$
>1. We say that $f$ is **injective** (one-to-one) iff for $x\neq y \ f(x)\neq f(y)$
> $\qquad$$\qquad$$\qquad$$\qquad$$\qquad$$\qquad$$\qquad$$\qquad$$\iff$"$f(x)=f(y)\iff x=y$"
>
>2. We say that f is **surjective** (onto) iff for every $y\in B$, there exists $x\in A$ s.t. $f(x) = y$
>		iff $f^{-1} (\{y\})\neq \ \emptyset \  \forall \ y\in B$
>		iff $f(A)=B$
>		
>3. We say that f is **bijective** if it is both **injective** and **surjective**

>[!n] Notation
$f: A\rightarrow B$
>- A is called the domain of $f$
>- $f(A)$ is the range of $f$

>[!r] Proposition 
>1) If f is injective then $E=f^{-1}(f(E))$ for every $E\subseteq A$
>In fact,
>	f is injective $\iff E=f^{-1}(f(E)) \ \forall \ E\subseteq A$
>2) If f is surjective then $H=f(f^{-1}(H))\forall H\subseteq B$
>In fact,
>	f is surjective $\iff H=f(f^{-1}(H))$
>		(ex) $\forall H\subseteq B$

>[!pf] Given f injective I want to show that $E=f^{-1}(f(E))$
>$\underline{E\subseteq f^{-1}(f(E))}$: done (independently of injectivity)
>
>$\underline{f^{-1}(f(E))\subseteq E}$:
>$$
\begin{align*}
Take\ x\in f^{-1}(f(E))\ then\ f(x)\in f(E)\ then\\
f(x)=f(x')\ for\ some\ x'\in E\\
but\ f\ is\ injective\ then\ x=x'\in E\\\\
Conclusion:\ E=f^{-1}(f(E))
\end{align*}
>$$
>
>>[!pf] Proof
$(\Rightarrow)$ done
$(\Leftarrow)$ Assume $f(x)=f(y)$, $x\in f^{-1}(f\{y\}) = \{y\}$
> then $x=y$

### Schroeder-Bernstein Theorem
>[!def] Given two sets A and B
>If there exists $f: A\rightarrow B$ injective and $g:B\rightarrow A$ injective
>then there exists a bijection $h:A\rightarrow B$

>[!n] If $f:A\rightarrow B$ bijective
>We use the notatoin $f^{-1}$ to denote the inverse map $f^{-1}:B\rightarrow A$ defined as follows:
>$$
>f^{-1}(b)=a\iff f(a)=b
>$$

>[!r] Idea
>![[diagram-20240124.svg]]
Here we have:
>$$
\begin{align*}
A_{0}&=A\textbackslash g(B)\\
A_{1}&=g(f(A_{0}))\\
A_{2}&=g(f(A_{1}))\\
\vdots\\
A_{n+1}&=g(f(A_{n}))\ \ \text{for n=0,1,2,...}\\
\vdots\\
A_{\infty}&= A_{0}\cup A_{1}... \ \ \text{(guests that i moved)}
\end{align*}
>$$
Let $h:A\rightarrow B$
>$$
h(x)=
\begin{cases}
f(x)&x\in A_{\infty} \\
g^{-1}(x)&x\notin A_{\infty}
\end{cases}
>$$
We show that h is injective
>
>Assume $h(x)=h(y)$ for $x,y\in A$     "( N.T.S. $x=y$ )"
>$$
\begin{align*}
&\underline{\text{Case 1:}}\ x,y\in A_{\infty}\\
& \;\;\;\;\;\;\;\; \text{then }h(x)=h(y)\Rightarrow f(x)=f(y)\text{ but $f$ is injective then }x=y\\\\
&\underline{\text{Case 2:}}\ x,y\notin A_{\infty}\\
&\;\;\;\;\;\;\;\;\text{then }h(x)=h(y)\Rightarrow g^{-1}(x)=g^{-1}(y)\Rightarrow x=y \text{ (by injectivity)}\\
\\
&\underline{\text{Case 3:}}\ x\in A_{\infty}\text{ and }y\notin A_{\infty}\text{ (or vice versa)}\\
&\;\;\;\;\;\;\;\; h(x)=h(y)\\
&\;\;\;\;\;\;\;\;\Rightarrow f(x)=g^{-1}(y))=y\\
&\;\;\;\;\;\;\;\;\Rightarrow g(f(x))=g(g^{-1}(y))=y\\
&x\in A_{\inf}=A_{0}\cup A_{1}\cup A_{2}\cup ...\\
&\text{ then }x\in A_{k}\text{ for some }k=0,1,2,3,...\\
&\text{ then }y=g(f(x)\in g(f(A_{k}))=A_{k+1}\subseteq A_{\infty}\text{ then }y\in A_{\infty}. \\\\
&\textbf{\;\;\;Contradiction!}\\
&\text{We conclude that $h$ is injective.}\\
\end{align*}
>$$
It remains to show that h is surjective.
Let $z\in B, x^{*}=g(z)$
>$$
\begin{align*}
&\underline{\text{Case $x^{*}\notin A_{\infty}$}}:h(x^{*})=g^{-1}(x^{*})=g^{-1}(g(z))=z\\
&\underline{\text{Case $x^{*}=g(z)$}}: \text{Notice that $x^{*}=g(z)\in g(B)$ and $A_{0}\cap g(B)=\emptyset$}\\
&\text{Then }x^{*}\notin A_{0}\text{ so}x^{*}\in A_{1}\cup A_{2}\cup...\\
&\text{Then }x^{*}\in A_{k}\text{ for some }k=1,2,3...\\
&\;\;\;\;\;\;\;\;(A_{k}==g(f(A_{k-1})))\\
&\text{Then }x^{*}=g(f(x'))\text{ for some }x'\in A_{k-1}\\\\
&\text{We have}\\
&x^{*}=g(f(x'))=g(z)\text{ but g is injective}\\
&\text{then }z=f(x')\\
&\text{but }x'\in A_{k-1}\subseteq A_{\infty}\text{ then }h(x')=f(x')\\
&\Rightarrow z=h(x')
\end{align*}
>$$

### Orders and Peanu Axioms
>[!def] Definition
>Given a set $S$, a (strict total) order denoted by "$\lt$" is a relation from $A$ to $A$ to satisfy the following:
>1. Given $x,y\in A$ we have exactly one of the following:
>$$
x<y\  \text{ or }\  y<x \ \text{ or }\  x=y \ \;(\text{Comparability})
>$$
>2. If $x<y$ and $y<z$ then
>$$
x<z
>$$
>
>>[!ex]
>>$$
\begin{align*}
A=\{a,b\}\\
&<=\{(a,a),(a,b)\}\text{ not strict order since we have $a<a$ and $a=a$}\\\\
A=\{a,b,c\}\\
&<_{1}=\{(a,b),(a,c)\}\text{ not an order since $b$ and $c$ are not comparable}\\
&<_{2}=\{(a,b),(a,c),(b,c)\}\\
&<_{3}=\{(a,b),(b,c),(c,a)\}\text{ not an order bc $a<b$ and $b<c$} \\
&\qquad \quad\text{but we don't have $a<c$}
\end{align*}
>>$$

>[!def] Given a set $A$ and an order < on $A$, we say that $(A,<)$ is an ordered set (totally)

>[!n] Given an ordered set $(A,<)$
>"$a\leq b$" means $a<b$ or $a=b$
>"$a\geq b$" means $b\leq a$

>[!def] The set on natural numbers $\mathbb{N}$ is defined by the following axioms:
>$$
\begin{align*}
&(P.1) \ 1\in \mathbb{N}\\\\
&(P.2)\ \text{If }n\in \mathbb{N}\text{, the successor }n+1\in \mathbb{N}\\\\
&(P.3)\ \text{If }n+1=M+1\text{ then }n=m\text{ (no two elements have the same successor)}\\\\
&(P.4)\ \text{1 is not the successor of any element.}\\\\
&(P.5)\ \text{Mathematical induction says:}\\\\
&\quad \quad \text{If }S\subseteq \mathbb{N}\text{ such that:}\\
&\quad \quad \quad i) 1\in S\\
&\quad \quad \quad ii) \text{if }k\in S\text{ then }k+1\in S\\
&\text{Then }S=\mathbb{N}
\end{align*}
>$$ 
>>[!r] P.5: Induction:
>>Assume I have a set of elements $P(n)$
>>$$
>>S=\{n\in \mathbb{N}:P(n)\text{ is true }\}
>>$$
>>If:
>>$\underline{\text{Base case: }} P(1)\text{ true }(1\in S)$
>>
>>$\underline{\text{Inductive step: }}$"$P(n)$ true" $\Rightarrow$ "$P(n+1)$ true" ($n\in S$ then $n+1\in S$)
>>Then from P.5 $S=\mathbb{N}$ $P(n)$ is true for every $n\in \mathbb{N}$.
>>
>>


>[!def] Def
> $m,n\in \mathbb{N}$
> $$
\begin{align*}
m+n&= \underbrace{(((n+1)+1)+1)+....+1)}_{\text{m times}}\\\\
m . n&= \underbrace{m+m+m+m+m+....+m}_{\text{n times}}
\end{align*}
>$$
>
>Order
>We say that
>$$
\begin{align*}
m&<n \text{ if and only if $n$ is "a successor" of $m$}\\
n&=m+k \text{ for some $k\in \mathbb{N}$}
\end{align*}
>$$
>($\mathbb{N}, <$) is an order

>[!ex] Induction Example
>$$
>2^{n}(n+1)! \;\;\; \forall \;\;\; n\in \mathbb{N}
>$$
>$n!=1.2.3.....n$
>>[!pf] $P(n)=\{2^{n}\leq (n+1)!\}$
>>$\underline{\text{Base case: }}$n=1
>>$$
>>\begin{align*}\\
2^{1}=2 && 2^{1}(1+1)!\\
(1+1)!=2!=2.1=2&& \text{verifies}
\end{align*}
>>$$
>>$\underline{\text{Inductive step: }}$Assume $P(k)$ is true for some $k\in \mathbb{N}$
>>$$
\begin{align*}
2^{k}\leq (k+1)!&&\text{I want to show that}\\
P(k+1)\text{ is true}&&\text{ i.e. }2^{k+1}\leq (k+1+1)!\\\\
2^{k+1}=2^{k}.2&\leq &(k+1)!(2)\leq (k+1)!(k+2)=(k+2)!\\
\end{align*}
>>$$
>>Then $P(n)$ is true for every $n\in \mathbb{N}$
>


>[!r] Strong Induction
>If $S\subseteq \mathbb{N}$ s.t.
> $\;\;\;\;$i) $1\in S$
>$\;\;\;\;$ii) If $1,2,3,...k\in S$ then $k+1\in S$
>Then $S=\mathbb{N}$
>
><u>In terms of statement.</u>
>Given a statement $P(n) \ \in \mathbb{N}$
>
>$\;\;\;\;\underline{\text{Base case: }}P(1)$ is true
>
>$\;\;\;\;\underline{\text{Inductive step: }}$
>$\;\;\;\;\;\;\;\;$If $P(1), P(2),...,P(k)$ are true then $P(k+1)$ is true
>
><u>Conclusion:</u> $P(n)$ is true $\forall \ n\in \mathbb{N}$
>>[!pf] Proof
>>Take
>>$T={n\in S:\{1,2,...,n\}\subseteq S}$ ($T\subseteq S\subseteq \mathbb{N}$)
>>
>><u>Base case:</u> $1\in T$ since by hypothesis $1\in S$, so $\{1\}\subseteq S$
>>
>><u>Inductive step:</u> Assume $k\in T$, then $\{1,2,....k\}\subseteq S$
>>$\;\;\;\;$Then by hypothesis (ii)$\;\;\;\;k+1\in S$
>>$\;\;\;\;$then $\{1,2,....,k,k+1\}\subseteq S$
>>$\;\;\;\;\Rightarrow k+1\in T$
>>by induction $T=\mathbb{N}$ and $S=\mathbb{N}$


>[!ex] Exercise
>Given $m,n\in \mathbb{N}$m we say that $n$ divides $m$, $n|m$m iff there exists $k\in \mathbb{N}$ s.t. $m=kn$
>$\;\;\;\;\underline{\text{Ex: }}2|4, 2|16$ since $16=2\times 8$
>
>We say that $p\geq 2$ is "prime number if and only if the only divisers of $p$ are $1$ and $p$".
> $\;\;\;\;\underline{\text{ex:}}$ 16 isn't prime but 17 is

>[!def] Theorem
>If $n\geq 2$ then $n$ can be factorized into prime numbers i.e. we can write
>$$n=p_{1}p_{2}p_{3}...p_{k}\text{ with }p_{1},p_{2},p_{3},...,p_{k}\text{ primes}$$
>>[!pf] Proof
>>$$
>>\begin{align*}
\underline{n=2:}&\text{ 2 is prime}\\
\underline{\text{Inductive step: }}&\text{Assume the statement is true for }2,3,4,...,k\\
&\text{Need to show it for }k+1\\
\underline{\text{Case 1: }}&k+1\text{ is prime. }k+1=k+1\\
\underline{\text{Case 2: }}&k+1\text{ is not prime. }then\\
&k+1=m.n \;\; \text{with }2\leq m, n\leq b\\\\
\text{But $P(m)$}& \text{ and $P(n)$ are true then}\\\\
&m=p_{1}p_{2}...p_{k}\text{ prime then }k+1=p_{1}...p_{k}\ q_{1}...q_{s}\\
&n=q_{1}q_{2}...q_{s}\\\\
\text{Then } S=\mathbb{N}
\end{align*}
>>$$

>[!r] Proposition: <u>Well-ordering principle</u>
>If $S$ is a nonempty subset of $\mathbb{N}$ then $S$ has a least element.
>$\;\;\;\;$i.e. there exists $n\in S$ s.t.
>$$n\leq x\text{ for every }x\in S$$
>We write $n=min(S)$
>>[!pf] Proof
>>We will show it with strong induction.
>>Take $P(n) = \{n\in S \ \Rightarrow \ S$ has a least element}
>>i) <u>Base case:</u> Is $P(1)$ true?
>>$\;\;\;\;$If $1\in S$ then 1 is the smallest element of $S$ by (p.4)
>>ii) <u>Inductive step:</u> Assume $P(1),P(2),P(3),...,P(k)$ are true
>>$\;\;\;\;$We need to show that $P(k+1)$ is true
>>$\;\;\;\;$ Assume $k+1\in S$
>>$$
>>\begin{align*}
\;\;\;\;\;\;\underline{\text{Case 1:}}&\ \{1,2,...,k\}\cap S=\emptyset \qquad\text{then k+1} \text{is the least element}\\
\;\;\;\;\;\;\underline{\text{Case 2:}}&\ \{1,2,...,k\}\cap S\neq \emptyset \qquad \text{then } \exists \ p\in \{1,...,k\}\\
&\;\;\;\;\;\; \text{s.t. $p\in S$ but $P(p)$ is true then $S$ has a least element.}\\
\end{align*}
>>$$
>><u>Conclusion:</u> $P(n)$ is true for every $n\in \mathbb{N}$
>>$\;\;\;\;$but $S\neq \emptyset$ i.e. $\exists \ n_{0}\in S$ and $P(n_0)$ is true then $S$ has a least element.



>[!def] Theorem
>Induction $\iff$ Strong Induction $\iff$ Well-ordering principle
>>[!pf] Proof
>>We showed
>>$\;\;\;\;$Induction $\Rightarrow$ Strong Induction $\Rightarrow$ Well-ordering principle
>>We show that
>>$\;\;\;\;$Well-ordering principle $\Rightarrow$ Induction
>>
>>Let $S\subseteq \mathbb{N}$ s.t. 
>>$\quad$i) $i\in S$
>>$\quad$ii) $k\in S \ \Rightarrow \ k+1\in S$
>>I need to prove that $S=\mathbb{N}$
>>
>>Assume $S$ is a proper subset of $\mathbb{N}$ i.e. $S\subset \mathbb{N}$
>> Then $\mathbb{N}\ \diagdown \ S\neq \emptyset$ then by the Well-ordering principle, $\mathbb{N}$ has a least element
>> 
>> $\qquad p=min(\mathbb{N} \ \diagdown \ S)$
>> 
>> $p\neq 1$ since $1\in S$ then $\exists \ k\in \mathbb{N}$ s.t.
>> 
>> $k+1=p \ , \ k<p$
>> 
>> so $k\notin \mathbb{N} \ \diagdown \ S$ then $k\in S$
>> 
>> by the inductive hypothesis, $k+1\in S$
>> 
>> $\mathbb{N} \ \diagdown \ S=\emptyset \ , \ S=\mathbb{N}$
>> 
>> $\qquad \qquad \qquad \qquad$ Contradiction!

---

### <u>Equivalence relations</u>: Construction of $\mathbb{Z}$.

>[!def] Given a set $A$
> An equivalence relation $R$ is a relation on $A$ (relation from $A$ to $A$)
> s.t:
>1) Reflexive: $a R a \quad \forall a \in A$
>2) Symmetry: $a R b \rightarrow b R a$
>3) Transitivity: $a R b$ and $b R c \Rightarrow a R c$.
>
>>[!ex] Example:
>>$$
\begin{align*}
& ''='' \text{ is an equivalence relation on }A\\
&''\leq'' \text{ isn't necessarily an equivalence relation since }a\leq b \text{ doesn't imply } b\leq c\\
&''<'' \text{ isn't an equivalence relation since it's not reflexive}
\end{align*}
>>$$
>

>[!ex] $\mathbb{N}\times \mathbb{N}$
>
>$$
(x, y) R\left(x^{\prime}, y^{\prime}\right) \Leftrightarrow x=x^{\prime} \quad \cong
>$$
i) $(x, y) R(x, y)$ since $x=x$
>
ii) If $(x, y) R(x, y)$ then $x=x^{\prime}$ then $(x',y')R(x,y)$
>
iii) If  $(x, y) R(x', y') \leftrightharpoons(x', y') R\left(x'', y^{\prime \prime}\right)$
>$\qquad$$\text { then } x=x^{\prime} \text { and } x^{\prime}=x^{\prime \prime}$
$\qquad$$\text { then } x=x^{\prime \prime}$
$\qquad$$\text { then }(x, y) R\left(x^{\prime \prime}, y^{\prime \prime}\right)$


>[!def]  Definition
>Given a set $A$ and an equivalence relation $R$, we define the equivalence classes
>$$
\text {for }a\in A\;\;\;[a]=\{b \in A ; a R b\}
>$$


>[!ex] Back to an example
>$$
\begin{aligned}
& {[(1,1)]=\{(1,1),(1,2),(1,3), \ldots,(1, n), \ldots\}} \\
& {[(2,1)]=\{(2,1),(2,2),(2,3), \ldots,(2, n), \ldots\}} \\
&\vdots\\
& {[(k,1)]=\{(k, n): n \in \mathbb{N}\} }
\end{aligned}
>$$

>[!def] Definition
>Given a set $A$, and an equivalence relation $R$ on $A$, the quotient set $A/R$ is the set of equivalences classes
>
>in the case above
>$$
\mathbb{N}\times \mathbb{N} / \mathbb{R}=\{[(1,1)],[(2,1)], \ldots \}
>$$


>[!r] Proposition
>Equivalence classes are either disjoint or equal.
>
>In fact, a set $A$ can be written as disjoin union of the corresponding equivalence classes
>
>>[!pf] 
>>Given two equivalence classes $[a]$ and $[b]$
>>
>>Assume $[a]\cap [b]\neq \emptyset$
>>then $\exists \ x\in [a]\cap[b]$
>>then $x\in [a]$ and $a\in [b]$
>>then $xRa$ and $xRb$
>>then ?? $aRb \text{ and so }[a]=[b]$

>[!def] Definition
>Define the following relation on $\mathbb{N}\times \mathbb{N}$
>$$
(a,b)R(c,d) \iff a+d=b+c
>$$
>>[!ex] Ex: $(1,2)R(2,3)$ since $1+3=2+2$
>><u>R is an equivalence relation</u>
>>>[!pf] Proof
>>>1) <u>Reflexive:</u>$\;\;$(a,b)R(a,b)
>>>$\qquad$$\qquad$true since $a+b=b+a$
>>>
>>>
>>>2) <u>Symmetric:</u>$\;\;$If $(a,b)R(c,d)$
>>>$\qquad$$\qquad$then $a+d=b+c$
>>>$\qquad$$\qquad$then $c+b=d+a$
>>>$\qquad$$\qquad$then $(c,d)R(a,b)$
>>>
>>>
>>>3) If $(a,b)R(c,d)$ and $(c,d)R(e,f)$
>>>$\qquad$$\qquad$$\iff a+d=b+c$
>>>$\qquad$and
>>>$\qquad$$\qquad$$\;\;$$c+f=d+e$
>>>$\qquad$$\qquad$$\iff a+d+c+f=b+c+d+e$
>>>$\qquad$$\qquad$$\iff a+f=b+e$
>>>$\qquad$$\qquad$$\iff (a,b)R(e,f)$

>[!r] The equivalence classes
>$$
>\begin{align*}
[(1,1)]= \{(1,1),(2,2),(3,3),\cdots\}&= \{(k,k):k\in \mathbb{N}\}\\
[(1,2)]= \{(1,2),(2,3),(3,4),\cdots\}&= \{(k,k+1):k\in \mathbb{N}\}\\
[(1,3)]= \{(1,3),(2,4),(3,5),\cdots\}&= \{(k,k+2):k\in \mathbb{N}\}\\
& \vdots\\
[(1,n+1)]=\{(1,n+1),(2,n+2),(3,n+3),\cdots\}&= \{(k,k+n):k, n\in \mathbb{N}\}\\
& \vdots\\
[(2,1)]= \{(2,1),(3,2),(4,3),\cdots\}&= \{(k+1,k):k\in \mathbb{N}\}\\
[(3,1)]= \{(3,1),(4,2),(5,3),\cdots\}&= \{(k+2,k):k\in \mathbb{N}\}\\
& \vdots\\
[(n+1,1)]=\{(k+n,k),\}\\
\end{align*}
>$$
>


### <u>Equivalence relations:</u> Construction of $\mathbb{Z}$

>[!n] Notation
>$$
\begin{align*}
[0]&:=[(1,1)= \{(k, k): k \in \mathbb{N}\}\\
[1]&:=[(1,2)= \{(k, k+1): k \in \mathbb{N}\}\\
\vdots\\
[n]&:=[(1, n+1)]= \{(k, k+n): k \in N\} \quad \text{ for } n \in \mathbb{N}\\
[-1]&:=[(2,1)= \{(k+1, k): k \in \mathbb{N}\}\\
\vdots\\
[-n]&:=[(n+1, 1)]= \{(k+n, k): k \in N\} \quad \text{ for } n \in \mathbb{N}\\
\end{align*}
>$$
>$$
\mathbb{Z}=\{[0],[1],[-1],[2],[-2],\cdots\}=\mathbb{N}\times \mathbb{N}/R
>$$

missing notes...

>[!r] R on $\mathbb{N} \times \mathbb{N}$
>$\qquad$$(a,b)$R$(c,d)$ $\iff$ $a+d=b+c$
>
>- [0],[(1,1)]=
>- [1]=[(1,2)]
>$\quad\;\vdots$
>- [n]=[(1,n+1)]
>- [-1]=[(2,1)]
>$\quad\;\vdots$
>- [-n]=[(n+1,1)]
>- [(a,b)]+[(c,d)]=[(a+c, b+d)]
>- [(a,b)].[(c,d)] = (bc+ad)
>$\quad\;\vdots$
>$\quad\;\vdots$
>$\mathbb{Z}=\{[0];[1];[-1];[2];[-2];\cdots\}$
>
>

>[!ex] Ex
>The product is well defined. (Exercise)
>$$
\begin{aligned}
& \cdot[m][n]=[m \cdot n] \\
& \cdot[1][x]=[x] \\
& \cdot[-1][n]=[-n] \\
& \cdot[-1][-n]=[n] \\
& \cdot[0][x]=[0]
\end{aligned}
>$$
>
>>[!pf] Proof
>>$$
\begin{aligned}
[1][x] & =[x] \\
{[1][x] } & =[(1,2)]=[(a, b)] \\
& =[(2 a+b, a+2 b)] \\
& =[(a, b)]
\end{aligned}
>>$$
>>Since $(a, b) R(2 a+b, a+2 b)$
>>
>>In fact, $a+(a+2 b)=b+(2 a+b)$
>>
>>Similarly, $[-1][n]:[-n]$
>>$\qquad \qquad\;\ [-1][-n]=[n]$
>>
>>
>>$$
\begin{aligned}
\underline  {[m][n]}  & =[m n] \\\\
{[m][n] } & =[(1, m+1)][(1, n+1)] \\
& =[(m+1+n+1,1+(m+1)(n+1)] \\
& =[(m+n+2, m n+m+n+2)] \\
& =[(1, m \ n+1)]
\end{aligned}
>>$$
>>
>>Since $(m+n+2, m n+m+n+2) R(1, m n+1)$
>>Similarly for the rest.
>>$$
[-x]:=[-1][x]
>>$$
>>we define
>>$$
[x]-[y]:=[x]+[-1][y]
>>$$


>[!def] Definition
><u>Order:</u>
>Define " $<$ " the order on $\mathbb{Z}$
>$$
[(a, b)]<[(c, d)]
>$$
>$$
\iff b+c<a+d
>$$
><u>Well Defined:</u> ie. we need to prove that
>if $b+c<a+d$
>and $\left(a^{\prime}, b^{\prime}\right) R(a, b)$
>$\qquad \left(c^{\prime}, d^{\prime}\right) R(c, d)$
>then
>$b^{\prime}+c^{\prime} < a^{\prime}+d^{\prime}$
>
>In fact, $b^{\prime}+c^{\prime}+b+c<b^{\prime}+c^{\prime}+a+d$ $=a^{\prime}+b+d^{\prime}+c$
>$\Rightarrow b^{\prime}+c^{\prime}\left\lt a^{\prime}+d^{\prime}\right.$ (by cancellation)
>
>
>"<"  is an order
>- Comparability: Given $[(a, b)],[(c, d)]$ in $\mathbb{Z}$
>from the order property on $\mathbb{N}$, we have comparability:
>$$
\begin{aligned}
b+c<a+d & \Rightarrow[(a, b)] < [(c, d)] \\
\text { or } b+c>a+d & \Rightarrow[(a, b)]>[(c, d)] \\
\text { or } b+c=a+d & \Rightarrow(a, b)R(c, d) \text { i.e. }[(a, b)]=[(c, d)]
\end{aligned}
>$$
>- Transitivity:ex

>[!r] Remark
>If $n,m \in \mathbb{N}$ s.t. $n<m$, then $[0]<[n]<[m]$
>>[!pf] Proof
>>$$
\begin{align*}\\
\underline{[0]<[n]}\\
[0]&= [(1,1)]\\
[n]&=[(1,n+1)]\\
[0]&<[n]\iff 1+1<1+n+1\\
& \qquad \;\;\; \iff 2<n+2 \qquad \text{(bc $n\in \mathbb{N}, \ n+2$ is a succ of $2$)}
\end{align*}
>>$$
>>$$
\begin{align*}\\
\underline{[n]<[m]}\\
[n]&= [(1,n+1)]\\
[m]&=[(1,m+1)]\\
[n]&<[m]\iff n+1<1+m+1\\
& \qquad \;\;\; \iff n+2<m+2\\
& \qquad \;\;\; \iff n<m
\end{align*}
>>$$


>[!def]
>Define $R$, the relation on $\mathbb{Z} \times \mathbb{N}$ as follows
>$$
\begin{align*}
\qquad(a, b)R(c, d)\\
\iff
\qquad a d=b c
\end{align*}
>$$
>$$
\begin{aligned}
& [(a, b)]+[(c, d)]=[(a d+b c, bd])] \\
& {[(a, b)] \cdot[(c, d))=[(a c, b d)]} \\
& {[(a, b)]<[(c, d)] \Rightarrow a d<b c} \\
& \cdots Q=\mathbb{Z} \times \mathbb{N} / R
\end{aligned}
>$$

### Cardinality

>[!def] Pigeonhole principle
>Notation: Let $n \in \mathbb{N}, \mathbb{N}_n=\{1,2,3, \cdots, n\}$
>
><u>Pigeonhole principle:</u>
>If $m>n$ in $\mathbb{N}$ then there is no injection
>$$
>f: \mathbb{N}_m \rightarrow \mathbb{N}_n
>$$
>
>>[!pf] Proof 
>>$P(n):\left\{m>n \Rightarrow\right. \ \ \nexists$  injection $\left.f: \mathbb{N}_m \rightarrow \mathbb{N}_n\right\}$
>>
>><u>Base case:</u> we prove $P(1)$ is true. i.e. if $m>1$, then there is as injection from $\mathbb{N}_m$ to $\mathbb{N}_1=\{1\}$
>>$$
>>\begin{aligned}
>>& \text { Let } f: \mathbb{N}_m \rightarrow \mathbb{N}_1=\{1\} \qquad , \quad \mathbb{N}_m = \{1,2,\cdots,m\}\\
>>& f(1)=1 \\
>>& f(2)=1 \text { so $f$ isn't injective }
>>\end{aligned}
>>$$
>>
>><u>Inductive step:</u> Assume $P(n)$ is true for some $n$
>>By contradiction, assume $P(n+1)$ is false. ie. there exists an injection
>>$$
>>f: \mathbb{N}_{m_0} \rightarrow \mathbb{N}_{n+1} \text { for some } m_0>n+1
>>$$
>>
>><u>Case 1:</u> $n+1 \notin f\left(\mathbb{N}_{m_0}\right)$
>>ie. $f\left(\mathbb{N}_{m_0}\right) \subseteq \mathbb{N}_n$
>>ie. $f$ is an injection from $\mathbb{N}_{m_0}$ to $\mathbb{N}_n$, but $m_0>n+1>n$. contradiction. Since $P(n)$ $\rightarrow$ true
>>
>><u>Case 2:</u> $n+1 \in f\left(\mathbb{N}_{m_0}\right)$ 
>>$$
\begin{aligned}
& \exists p \in \mathbb{N}_{m_0} \text { sit } f(p)=n+1 \\
& \mathbb{N}_{m_0}=\left\{1,2,3, \cdots, p-1, p, p+1, n, \cdots, m_0\right\} \\
& \mathbb{N}_{m_1}=\{1,2,3, \cdots, n, n+1\} (\text{from $p$ to $n+1$ for ex})
\end{aligned}
>>$$
>>
>>Define $g: \mathbb{N}_{n_0-1} \rightarrow \mathbb{N}_n$
>>$$
>>g(k)= \begin{cases}f(k) & k \leq p+1 \\ f(k+1) & k=p, \ldots, m_0-1\end{cases}
>>$$
>>
>>Injection. but $m_0-1>n$. Contradiction.
>>Conclusion: $P(n)$ is always true


>[!r] Pigeonhole Principle (infinite case)
>There exists no injection
>$$
>f: \mathbb{N} \rightarrow \mathbb{N}_n \text { for any } n \in \mathbb{N}
>$$
>
>>[!pf] Proof
>>Assume $f: \mathbb{N} \rightarrow \mathbb{N}_n$ infective.
>>Take $g: \mathbb{N}_{n+1} \rightarrow \mathbb{N}_n$
>>$\qquad \qquad g(k)=f(k)$
>>$\qquad \;\; g=\left.f\right|_{N_{n+1}}$
>>
>>$g$ is injective. contradiction since $n+1>n$

>[!def] Definition
>Given a non-empty set $A$.
We say $A$ is finite iff $\exists f: A \rightarrow N_n$ is bijective for some $n \in \mathbb{N}$ in this case we write $card \ A=n$
>
>Otherwise we say that $A$ is an infinite set.
>
><u>By convention:</u> $\emptyset$ is a finite set and card $\emptyset=0$
>Why well defined ? : Assume $f: A \rightarrow \mathbb{N}_n$
>$$
>g: A \rightarrow \mathbb{N}_m
>$$
>$\qquad$bijective for $m>n$
>then
>$$
>f \circ g^{-1}: \mathbb{N}_m \rightarrow \mathbb{N}_n
>$$
>$\qquad$bijective
>
>Contradiction to the pigments principle.
>
>Corollary: $\mathbb{N}$ is an infinite set

