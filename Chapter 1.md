---
cssclasses:
  - academic
---
>[!def] Definition
>Given an ordered set $(S,<)$
>We say that $S$ has the least upper bound property if and only if for every nonempty subset $E$ of $S$ that is bounded above, $sup \ E$ exists.
>>[!ex] Ex
>>- $\mathbb{Q}$ doesn't have the l.u.b. property.
>>- $\mathbb{N}$ the greatest lower bound property by the well-ordering principle.
>>In fact, in this case, every nonempty set $E\subseteq \mathbb{N}$ is bounded below and $inf \ E\in E$
>>- $\mathbb{Z}$ has the greatest lower bound property.
>>Let $E\subseteq \mathbb{Z}$ that is bounded below.
>>Let $x_0$ be a lower bound of $E$.
>>$\qquad$$x_{0}\leq k$ for e very $k\in E$
>>$\qquad$$\{k-x_0 +1:k\in E\}\subseteq \mathbb{N}$
>>$\quad$It has an infimum $\quad n_0=k_0-x_{0}+1\leq k-x_0+1$
>>$\quad$in the set $\qquad \Rightarrow k_{0} \leq k$ for all $k\in E$ but $k_{0}\in E$ then $inf\ E=k_0$
>>
>>In fact, for every $E\subseteq \mathbb{Z}$ bounded below.
>>$\qquad$$inf\ E$ exists and belongs to $E$.
>>

>[!def] Theorem
>$$
>\begin{align*}
&(S,<) \text{ has the l.u.b. property}\\
 & \qquad \qquad \iff\\
&(S,<) \text{ has the g.l.b. property}
\end{align*}$$
>>[!pf] Proof
>>$(\Rightarrow)$ Take $E\subseteq S$ that is bounded below.
>>
>>Then $A= \{x\in S:x \text{ is a lower bound of }E\}$ is nonempty.
>>
>>$a_{0}=sup \ A$ means $a_{0}$ is the least upper bound of $A$.
>>$E\neq \emptyset$ then it has an element $x_{0}\in E$ for every $a\in A$, $a$ is a lower bound of $E$.
>>$\quad$i.e. $a\leq x_0$ for every $a\in A$
>>$A$ is bounded above by $x_0$
>>
>>Since $(S,<)$ has the l.u.b property \, $sup \ A$ exists. Call it $a_0$.
>>
>>N.T.S. that $a_{0}=inf\ E$
>>
>>Take $a\in A$ then $a\leq x$ for every $x\in E$.
>>$\quad$ then $x$ is an upper bound of $A$
>>$\quad$ then $a$ is a lower bound of $E$.
>>
>>then every $x\in E$ is an upper bound for $A$.
>>but $a_{0}$ is the least upper bound of $A$
>>
>>then $a_{0}\leq x$ for every $x\in E$
>>$\qquad a_0$ is a lower bound of $E$
>>
>>We need to show that $a$ is the greatest lower bound of $E$.
>>$\qquad$then by definition this is done.
>>$$
>>a_0 \rightarrow sup \ A
>>$$


>[!def] Theorem 
>There exists an ordered field containing
>
>$\mathbb{Q}$ the admits the l.u.b property. 
>(where addition and multiplication are compatible)
>
>In fact, this field is unique up to isomorphism.
>$\qquad$We call it the set of real number $\mathbb{R}$
>

### Construction of $\mathbb{R}$

A Dedekind cut is a set $A\subseteq \mathbb{Q}$ s.t.
$$
\begin{align*}
&I)A\neq \emptyset, A\subset \mathbb{Q}\\\\
&II)\text{ If }p\in A\text{ then for every }q<p\text{ we have }q\in A\\
&III)\text{If }p\in A\text{ then }\exists \; r\in A\text{ s.t. }\; r>p
\end{align*}$$
>[!ex] Example
>$E=\{x:x<1\}$$\quad$a cut
>$\qquad$$\qquad$$III: \quad p\in E$ then $\frac{p+1}{2}\in E$
>In general if $p_{0\in}\mathbb{Q}$,
>$$
>\{a:a<p_0\}\text{ Is a cut which will represent the number }p_0
>$$
>2) $E=\{x\in \mathbb{Q}:x^{2}<2\} \qquad$ not a cut it violates $II$
>3) $E=\{x\in \mathbb{Q}:x \leq \text{ or }x^2<2\} \qquad$ A cut ({$\sqrt{2}$})
>
>The set of all cuts is called $\mathbb{R}$.
>We say $A<B$ if and only if $A\leq B$
>
>$p<q$ in $\mathbb{Q}$ $\quad$$\{x<p\}\subset \{x<q\}$
>$\qquad$$\qquad$$\qquad$$\{x<p\}<\{x\subset q\}$



