(*<*)
theory  T8TeoriaHintikkaP
imports T7ConjuntoMaximalP
begin
(*>*)

subsection \<open> Conjuntos de Hintikka y modelos de Hintikka\<close>

text \<open>
  \label{hintikka}
  En esta sección introducimos el concepto de conjunto de
  Hintikka y demostramos que en un lenguaje proposicional, cualquier
  subconjunto de un {\em {conjunto de Hintikka}} es {\em satisfacible}.

\<close>
text \<open>
  \begin{definicion}\label{DefhintikkaP}
  Un conjunto $H$ de fórmulas proposicionales es un {\bf{conjunto de
  Hintikka}} si cumple las siguientes condiciones:
  \begin{enumerate}
  \item Para cualquier fórmula atómica $P$, $P\notin H$ o $\neg P\notin H$.
  \item $\bot\notin H$ y $\neg \top\notin H$.
  \item Si $\neg \neg F \in H$ entonces $F\in H$.
  \item Si $\alpha\in H$ entonces, $\alpha_1 \in H$ y $\alpha_2 \in H$.
  \item Si $\beta\in H$ entonces, $\beta_1\in H$ o $\beta_2\in H$.
  \end{enumerate}
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition hintikkaP :: "'b formula set \<Rightarrow> bool" where
  "hintikkaP H = ((\<forall>P. \<not> (Atomo P \<in> H \<and> (\<not>.Atomo P) \<in> H)) \<and>
                 FF \<notin> H \<and> (\<not>.TT) \<notin> H \<and>
                 (\<forall>F. (\<not>.\<not>.F) \<in> H \<longrightarrow> F \<in> H) \<and>
                 (\<forall>F. ((FormulaAlfa F) \<and> F \<in> H) \<longrightarrow>
                      ((Comp1 F) \<in> H \<and> (Comp2 F) \<in> H)) \<and>
                 (\<forall>F. ((FormulaBeta F) \<and> F \<in> H) \<longrightarrow>
                      ((Comp1 F) \<in> H \<or> (Comp2 F) \<in> H)))"

subsection \<open> Satisfactibilidad de conjuntos de Hintikka \<close>

text\<open>
  \label{interpretacionhintikka}
  En esta sección mostramos que cualquier conjunto de Hintikka
  proposicional tiene un modelo (definición \ref{modeloP}). Para la
  demostración, a cada conjunto de Hintikka le asocia\-mos una {\em
  interpretación de Hintikka}.

  \begin{definicion}
  Sea $H$ un conjunto de fórmulas proposicionales, definimos la
  interpretación $I_H$ como sigue: sea $P$ un símbolo proposicional,
  entonces
  \newline \hspace*{1cm}
  \[I_H(P) = \begin{cases}
             \V, & \text{si $P\in H$} \\
             \F, & \text{en otro caso.}
           \end{cases}
  \]

  Si $H$ es un conjunto de Hintikka, $I_H$ es llamada una
  {\bf{interpretación de Hintikka}}.
  \end{definicion}

\<close>
text \<open>
  La formalización en Isabelle de la interpretacion $I_H$ es la siguiente:
\<close>

fun IH :: "'b formula set  \<Rightarrow> 'b \<Rightarrow> v_verdad" where
  "IH H P = (if Atomo P \<in> H then Verdad else Falso)"

text \<open>

  A continuación demostramos que si $H$ es de Hintikka entonces $I_H$ es
  un mode\-lo de $H$.  Para la demostración probamos por inducción bien
  fundamentada sobre el {\em tamaño} de una fórmula la siguiente
  afirmación equivalente: {\em dado un conjunto de Hintikka} $H$,
  {\em si} $F\in {H}$ {\em entonces} $I'_H(F)=\V$, {\em y} {\em si}
  $\neg F\in H$ {\em entonces} $I'_H(\neg F)=\V$.

  En general, si tenemos una relación $\prec$ bien fundamentada en un
  conjunto $A$ y una propiedad $P$ sobre $A$, la regla de inferencia por
  inducción bien fundamentada se enuncia de la siguiente manera:
  \[\begin{array}{c}
      [\forall y (y\prec x \Rightarrow P(y))]\\
      \vdots\\
      \displaystyle \frac{P(x)}{P(a)}
    \end{array}
  \]

  Es decir, para demostrar $P(a)$ para un elemento $a\in A$, es
  suficiente demostrar $P(x)$ para un $x$ arbitrario usando como
  hipótesis, si $y\prec x$ entonces $P(y)$.

  En Isabelle esta regla de inducción @{text "wf_induct"}, se expresa de
  la siguiente forma:

  \begin{center}
  @{thm[mode=Rule] wf_induct[no_vars]}
  \end{center}

  \noindent
  o también,

  \begin{center}
  @{thm wf_induct[no_vars]}
  \end{center}

  En donde {\em wf r} afirma que la relación $r$ es {\em bien
  fundamentada}.
\<close>

text \<open>
  \begin{teorema}\label{hintikkaP-model-aux}
  Sea $H$ un conjunto de Hintikka. Si $F\in {H}$ entonces
  $I'_H(F)=\V$, y si $\neg F\in H$ entonces $I'_H(\neg F)=\V$.
  \end{teorema}

  {\bf{Demostración:}}
  La demostración es por inducción bien fundamentada.  Para definir la
  relación bien fundamentada $\prec$ en el conjunto de fórmulas,
  conside\-ramos la función {\em tamaño}, que determina el tamaño de una
  fórmula.

\begin{definicion}\label{tamano} Sean $F$ y $G$ fórmulas, entonces
  \begin{itemize}
    \item tamaño(F) = 1 si $F$ es una fórmula atómica, $\bot$ o $\top$
    \item tamaño$(\neg F)$ = 1 + tamaño(F)\
    \item tamaño$(F\wedge G)$ = tamaño$(F\vee G)$ =
          tamaño$(F \rightarrow G)$ = 1+tamaño(F)+ tamaño(G)
  \end{itemize}
  \end{definicion}
\<close>

(*<*)
primrec tamano :: "'b formula \<Rightarrow> nat" where
  "tamano FF = 1"
| "tamano TT = 1"
| "tamano (Atomo P) = 1"
| "tamano (\<not>. F) = (tamano F) + 1"
| "tamano (F \<and>. G) = (tamano F) + (tamano G) + 1"
| "tamano (F \<or>. G) = (tamano F) + (tamano G) + 1"
| "tamano (F \<rightarrow>. G) = (tamano F) + (tamano G) + 1"

lemma ptamano: "0 < tamano F"
by (induct F) auto
(*>*)

text \<open>

  Así, la relación $\prec$ es igual a la imagen inversa de la relación
  en $\mathbb{N}$ inducida por la función de medida {\em tamaño},
  $$F \prec G \Longleftrightarrow \mbox{\em tamaño}(F)<\mbox{\em tamaño}(G).$$

  Puesto que la relación $<$ ({\em menor que}) en $\mathbb{N}$ es bien
  fundamentada entonces, $\prec$ es bien fundamentada.

  Sea $F$ una fórmula arbitraria, la hipótesis de inducción afirma que
  si $G \prec F$ entonces, si $G\in H$ entonces $I'_H(G) =\V$, y si
  $\neg G\in H$ entonces $I'_H(\neg G)=\V$.

  Hay que demostrar que,
  si $F\in H$, entonces $I'_H(F)=\V$ y
  si $\neg F\in H$, entonces $I'_H(\neg F) = \V$.

  La demostración es por casos en la fórmula $F$.

  {\bf{Caso 1:}} Supongamos que $F$ es la fórmula $\bot$.

  {\bf{Caso 1.a:}} Por hipótesis $H$ es un conjunto de Hintikka, luego
  $\bot\notin H$.  Por lo tanto la implicación, si $\bot\in H$ entonces
  $I'_H(\bot)=\V$, es verdadera.

  {\bf{Caso 1.b:}} Por definición,
  $I'_H(\neg \bot) = \neg I'_H(\bot)= \V$.
  Por lo tanto, la implicación, si
  $\neg \bot\in H$ entonces $\neg I'_H(\bot)=\V$, es verdadera.

  {\bf{Caso 2:}} Supongamos que $F$ es la fórmula $\top$.

  {\bf{Caso 2.a:}} Por definición, $I'_H(\top)=\V$. Por lo tanto la
  implicación, si $\top\in H$ entonces $I'_H(\top)=\V$, es verdadera.

  {\bf{Caso 2.b:}} Por hipótesis $H$ es un conjunto de Hintikka, luego
  $\neg {\top}\notin H$. Por lo tanto la implicación, si $\neg \top\in
  H$ entonces $I'_H(\neg \top)=\V$, es verdadera.

  {\bf{Caso 3:}} Supongamos que $F$ es la fórmula atómica $P$.

  {\bf{Caso 3.a:}} Supongamos que $P\in H$, entonces, por definición de
  $I_H$, $I'_H(P)=\V$.

  {\bf{Caso 3.b:}} Supongamos que $\neg P\in H$. Puesto que $H$ es de
  Hintikka, se tiene que $P\notin H$ o $\neg P \notin H$. Luego,
  $P\notin H$ ya que $\neg P \in H$. Por lo tanto $I'_H(P)= \F$, por
  definición de $I_H$.  De esta forma,
  $I'_H(\neg P) = \neg (I'_H(P)) = \V$.

  {\bf{Caso 4:}} Sea $F$ la fórmula $F_1 \wedge F_2$.

  {\bf{Caso 4.a:}} Supongamos que $F_1 \wedge F_2\in H$.  Puesto que $H$
  es de Hintikka se tiene que, $F_1 \in H$ y $F_2 \in H$.  También, por
  la definición del tamaño de una fórmula se tiene que
  $F_1 \prec (F_1 \wedge F_2)$ y $F_2 \prec (F_1 \wedge F_2)$,
  por consiguiente usando la hipótesis de inducción te\-nemos que las
  siguientes dos implicaciones son verdaderas:

  Si $F_1\in H$ entonces $I'_H(F_1)=\V$, y si $F_2\in H$ entonces
  $I'_H(F_2)=\V$.

  De esta forma, $I'_H(F_1)=\V$ y $I'_H(F_2) = \V$. Luego, por la
  definición del valor de una fórmula tenemos que,
  $I'_H(F_1\wedge F_2)= I'_H(F_1)\wedge I'_H(F_2) = \V$.

  {\bf{Caso 4.b:}} Supongamos que $\neg (F_1\wedge F_2)\in H$.  Puesto
  que $H$ es de Hintikka se tiene que,
  $\neg F_1 \in H$ o $\neg F_2 \in H$.  A partir de la anterior
  disyunción mostramos, por eliminación de la disyunción, que
  $I'_H(\neg (F_1\wedge F_2))=\V$.

  {\bf{Caso 4.b.1:}} Supongamos que $\neg F_1 \in H$.  Por la definición
  del tamaño de una fórmula se tiene que
  $\neg F_1 \prec (F_1 \wedge F_2)$ y por lo tanto por la hipótesis de
  inducción tenemos que la implicación, si
  $\neg F_1\in H$ entonces $I'_H(\neg F_1)=\V$ es verdadera.  De lo
  anterior, se tiene que $I'_H(\neg F_1)=\V$, es decir, $\neg
  (I'_H(F_1))=\V$.  Por lo tanto, $I'_H(\neg (F_1\wedge F_2)) = \V$.

  {\bf{Caso 4.b.2:}} Supongamos que $\neg F_2 \in H$. La demostración es
  igual que la del caso anterior.

  Los otros casos, cuando $F$ es $F_1 \vee F_2, F_1 \rightarrow F_2$ o
  $\neg F$, se demuestran en forma similar a los anteriores.
\<close>

(*<*)
text \<open>
  {\bf{Caso 5:}} Supongamos que $F$ es la fórmula $F_1 \vee F_2.$

  {\bf{Caso 5.a:}} Supongamos que $F_1 \vee F_2\in H$.  Puesto que $H$
  es de Hintikka se tiene que, $F_1 \in H$ o $F_2 \in H$.  A partir de
  la anterior disyunción mostramos, por eliminación de la disyunción,
  que $I'_H(F_1\vee F_2)=\V$.

  {\bf{Caso 5.a.1:}} Supongamos $F_1 \in H.$ Por la definición del
  tamaño de una fórmula se tiene que \linebreak
  $F_1 \prec (F_1 \vee F_2)$ y por lo tanto por la hipótesis de
  inducción tenemos que la implicación es verdadera, si
  $F_1\in H$ entonces $I'_H(F_1)=\V$. De lo anterior, $I'_H(F_1)=\V$.
  Por lo tanto, $I'_H(F_1\vee F_2) = I'_H(F_1)\vee I'_H(F_2)= \V$.

  {\bf{Caso 5.a.2:}} Supongamos $F_2 \in H.$ La demostración es igual
  que la del caso (a.1).

  {\bf{Caso 5.b:}} Supongamos que $\neg(F_1 \vee F_2)\in H$.  Puesto que
  $H$ es de Hintikka se tiene que, $\neg F_1 \in H$ y $\neg F_2 \in H$
  ya que $\neg(F_1 \vee F_2)\in H$.  Por la definición del tamaño de una
  fórmula se tiene que $\neg F_1 \prec (F_1 \vee F_2)$ y $\neg F_2 \prec (F_1 \vee
  F_2)$, por consiguiente usando la hipótesis de inducción tenemos que
  las siguientes dos implicaciones son verdaderas, si $\neg F_1\in H$
  entonces $I'_H(\neg F_1)=\V$, y si $\neg F_2\in H$ y $F_2$ entonces
  $I'_H(\neg F_2)=\V$.

  De esta forma, $I'_H(\neg F_1)=\V$ y $I'_H(\neg F_2)=\V$. Luego, por
  la definición del valor de una fórmula tenemos que,\\

  $\begin{array}{lll}
      I'_H(\neg (F_1\vee F_2)) & = & \neg I'_H(F_1 \vee F_2)\\
                               & = & \neg(I'_H(F_1)\vee I'_H(F_2))\\
                               & = & \neg I'_H(F_1)\wedge \neg I'_H(F_2)\\
                               & = & I'_H(\neg F_1)\wedge I'_H(\neg F_2)\\
                               & = & \V.\\
   \end{array}$

  {\bf{Caso 6:}} Supongamos que $F$ es la fórmula $F_1 \rightarrow F_2.$

  {\bf{Caso 6.a:}} Supongamos que $F_1 \rightarrow F_2\in H$.  Puesto
  que $H$ es de Hintikka se tiene que, $\neg F_1 \in H$ o $F_2 \in H$.
  A partir de la anterior disyunción mostramos, por eliminación de la
  disyunción, que $I'_H(F_1\rightarrow F_2)=\V$.

  {\bf{Caso 6.a.1:}} Supongamos $\neg F_1 \in H.$ Por la definición del
  tamaño de una fórmula se tiene que $\neg F_1 \prec (F_1 \rightarrow F_2)$ y
  por lo tanto por la hipótesis de inducción tenemos que la siguiente
  implicación es verdadera, si $\neg F_1\in H$ entonces $I'_H(\neg
  F_1)=\V$.

  De lo anterior, $I'_H(\neg F_1)=\V$, es decir, $\neg I'_H(F_1)=\V$.
  Por lo tanto, $I'_H(F_1\rightarrow F_2)= I'_H(F_1)\rightarrow
  I'_H(F_2) = \V$.

  {\bf{Caso 6.a.2:}} Supongamos $F_2 \in H.$ Por la definición del
  tamaño de una fórmula se tiene que $F_2 \prec (F_1 \rightarrow F_2)$ y
  por lo tanto por la hipótesis de inducción tenemos que la siguiente
  implicación es verdadera, si $F_2\in H$ entonces $I'_H(F_2)=\V$.  De
  lo anterior, $I'_H(F_2)=\V$.  Por lo tanto, $I'_H(F_1\rightarrow F_2)
  = I'_H(F_1) \rightarrow I'_H(F_2) = \V$.

  {\bf{Caso 6.b:}} Supongamos que $\neg(F_1 \rightarrow F_2)\in H$.
  Puesto que $H$ es de Hintikka se tiene que, $F_1 \in H$ y $\neg F_2
  \in H$.  Por la definición del tamaño de una fórmula se tiene que $F_1
  \prec (F_1 \rightarrow F_2)$ y $\neg F_2 \prec (F_1 \rightarrow F_2)$, por
  consiguiente usando la hipótesis de inducción tenemos que las
  siguientes dos implicaciones son verdaderas, si $F_1\in H$ entonces
  $I'_H(F_1)=\V$, y si $\neg F_2\in H$ entonces $I'_H(\neg F_2)=\V$.  De
  esta forma, $I'_H(F_1)=\V$ y $I'_H(\neg F_2)=\V$.

  Por lo tanto $I'_H(F_1) \rightarrow I'_H(F_2) = \F$.  Luego, por la
  definición del valor de una fórmula tenemos que, $I'_H(\neg (F_1
  \rightarrow F_2)) = \neg I'_H(F_1 \rightarrow F_2) = \neg (I'_H(F_1)
  \rightarrow I'_H(F_2))=\V .$

  {\bf{Caso 7:}} Supongamos que $F$ es la fórmula $\neg F.$

  {\bf{Caso 7.a:}} Supongamos que $\neg F\in H$.  Por la definición del
  tamaño de una fórmula se tiene que $F \prec \neg F$, por consiguiente
  usando la hipótesis de inducción tenemos que la siguiente implicación
  es verdadera, si $\neg F\in H$ entonces $I'_H(\neg F) = \V$. De esta
  forma, $I'_H(\neg F) = \V$.

  {\bf{Caso 7.b:}} Supongamos que $\neg \neg F\in H$.  Puesto que $H$ es
  de Hintikka se tiene que $F\in H$.  Por la definición del tamaño de
  una fórmula se tiene que $F \prec \neg F$, por lo tanto usando la
  hipótesis de inducción tenemos que la siguiente implicación es
  verdadera, si $F\in H$ entonces $I'_H(F) = \V$. De esta forma,
  $I'_H(F) = \V$. De esto último por la definición del valor de una
  fórmula se tiene que, $\neg \neg I'_H(F)= \V$.
\<close>

(*>*)
text \<open>
  Los diferentes casos del teorema anterior se formalizan por medio de
  los si\-guientes lemas.  La relación @{text "measure tamano"} en
  Isabelle corresponde a la formalización de la relación $\prec$.
\<close>

lemma casoP1:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, FF) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G)= Verdad)"
shows "(FF \<in> H \<longrightarrow> valor (IH H) FF = Verdad) \<and> ((\<not>.FF) \<in> H \<longrightarrow> valor (IH H) (\<not>.FF)=Verdad)"
(*<*)
proof(rule conjI)
  show "(FF \<in> H \<longrightarrow>  valor (IH H) FF = Verdad)"
  proof -
    have "FF \<notin> H" using hip1 by (unfold hintikkaP_def) auto
    thus "FF \<in> H \<longrightarrow> valor (IH H) FF = Verdad" by simp
  qed
  next
  show "(\<not>.FF) \<in> H \<longrightarrow> valor (IH H) (\<not>.FF)=Verdad"
  proof -
    have "valor (IH H) (\<not>.FF)= Verdad" by(simp add: v_negacion_def)
    thus ?thesis by simp
  qed
qed
(*>*)
text\<open> \<close>
lemma casoP2:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, TT) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G)= Verdad)"
shows
"(TT \<in> H \<longrightarrow> valor (IH H) TT = Verdad) \<and> ((\<not>.TT) \<in> H \<longrightarrow> valor (IH H) (\<not>.TT)=Verdad)"
(*<*)
proof(rule conjI)
  show "TT \<in> H \<longrightarrow> valor (IH H) TT = Verdad"
  by simp
  next
  show "(\<not>.TT) \<in> H \<longrightarrow> valor (IH H) (\<not>.TT)=Verdad"
  proof -
    have "(\<not>.TT) \<notin> H" using hip1 by (unfold hintikkaP_def) auto
    thus "(\<not>.TT) \<in> H  \<longrightarrow> valor (IH H) (\<not>.TT)=Verdad"
    by simp
  qed
qed
(*>*)
text\<open>\<close>
lemma casoP3:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, Atomo P) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G)= Verdad)"
shows "(Atomo P \<in> H  \<longrightarrow> valor (IH H) (Atomo P) = Verdad) \<and>
((\<not>.Atomo P) \<in> H \<longrightarrow> valor (IH H) (\<not>.Atomo P) = Verdad)"
(*<*)
proof(rule conjI)
  show "(Atomo P)  \<in> H \<longrightarrow> valor (IH H) (Atomo P) = Verdad" by simp
  next
  show "(\<not>.Atomo P) \<in> H \<longrightarrow> valor (IH H) (\<not>.Atomo P) = Verdad"
  proof(rule conjI impI)
    assume h1: "\<not>.Atomo P \<in> H"
    show "valor (IH H) (\<not>.Atomo P) = Verdad"
    proof -
      have "\<forall>p. \<not> (Atomo p \<in> H \<and> (\<not>.Atomo p) \<in> H)"
      using hip1 conjunct1 by(unfold hintikkaP_def)
      hence "Atomo P \<notin> H" using h1 by auto
      hence "valor (IH H) (Atomo P) = Falso" by simp
      thus ?thesis by(simp add: v_negacion_def)
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma casoP4:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, F1 \<and>. F2) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G) = Verdad)"
shows "((F1 \<and>. F2) \<in> H \<longrightarrow> valor (IH H) (F1 \<and>. F2) = Verdad) \<and>
((\<not>.(F1 \<and>. F2)) \<in> H \<longrightarrow> valor (IH H) (\<not>.(F1 \<and>. F2)) = Verdad)"
(*<*)
proof(rule conjI)
  show "((F1 \<and>. F2) \<in> H \<longrightarrow> valor (IH H) (F1 \<and>. F2) = Verdad)"
  proof(rule conjI impI)
    assume h2: "(F1 \<and>. F2) \<in> H"
    show  "valor (IH H) (F1 \<and>. F2) = Verdad"
    proof -
      have "FormulaAlfa (F1 \<and>. F2)" by simp
      hence "Comp1 (F1 \<and>. F2) \<in> H \<and> Comp2 (F1 \<and>. F2) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)
      hence "F1 \<in> H" and "F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      moreover
      have "(F1, F1 \<and>. F2) \<in> measure tamano" and
      "(F2, F1 \<and>. F2) \<in> measure tamano"
      by auto
      hence "(F1 \<in> H \<longrightarrow> valor (IH H) F1 = Verdad)" and
      "(F2 \<in> H \<longrightarrow> valor (IH H) F2 = Verdad)"
      using hip2 by auto
      ultimately
      have "valor (IH H) F1 = Verdad" and "valor (IH H) F2 = Verdad"
      by auto
      thus ?thesis by (simp add: v_conjuncion_def)
    qed
  qed
  next
  show "\<not>.(F1 \<and>. F2) \<in> H \<longrightarrow> valor (IH H)  (\<not>.(F1 \<and>. F2)) = Verdad"
  proof(rule impI)
    assume h2: "(\<not>.(F1 \<and>. F2)) \<in> H"
    show "valor (IH H) (\<not>.(F1 \<and>. F2)) = Verdad"
    proof -
      have "FormulaBeta (\<not>.(F1 \<and>. F2))" by simp
      hence "Comp1 (\<not>.(F1 \<and>. F2)) \<in> H \<or> Comp2 (\<not>.(F1 \<and>. F2)) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)
      hence "(\<not>.F1) \<in> H \<or> (\<not>.F2) \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      thus ?thesis
      proof(rule disjE)
        assume "(\<not>.F1) \<in> H"
        moreover
        have "(\<not>.F1, (F1 \<and>. F2)) \<in> measure tamano" using ptamano by simp
        hence "(\<not>.F1) \<in> H \<longrightarrow> valor (IH H) (\<not>.F1) = Verdad"
        using hip2 by simp
        ultimately
        have 1: "valor (IH H) (\<not>.F1) = Verdad" by simp
        hence "valor (IH H) F1 = Falso" using ValoresNegacion2 by auto
        thus "valor (IH H) (\<not>.(F1 \<and>. F2)) = Verdad"
        by (simp add: v_negacion_def, simp add: v_conjuncion_def)
        next
        assume "(\<not>.F2) \<in> H"
        moreover
        have "(\<not>.F2, (F1 \<and>. F2)) \<in> measure tamano" using ptamano by simp
        hence " (\<not>.F2) \<in> H \<longrightarrow> valor (IH H) (\<not>.F2)= Verdad"
        using hip2 by simp
        ultimately
        have 1: "valor (IH H) (\<not>.F2) = Verdad" by simp
        hence "valor (IH H) F2 = Falso" using ValoresNegacion2 by auto
        thus "valor (IH H) (\<not>.(F1 \<and>. F2)) = Verdad"
        by (simp add: v_negacion_def, simp add: v_conjuncion_def)
      qed
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma casoP5:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, F1 \<or>. F2) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G) = Verdad)"
shows "((F1 \<or>. F2) \<in> H \<longrightarrow> valor (IH H) (F1 \<or>. F2) = Verdad) \<and>
((\<not>.(F1 \<or>. F2)) \<in> H \<longrightarrow> valor (IH H) (\<not>.(F1 \<or>. F2)) = Verdad)"
(*<*)
proof(rule conjI)
  show "(F1 \<or>. F2) \<in> H \<longrightarrow> valor (IH H) (F1 \<or>. F2) = Verdad"
  proof(rule conjI impI)
    assume h2: "(F1  \<or>. F2) \<in> H"
    show "valor (IH H) (F1 \<or>. F2) = Verdad"
    proof -
      have "FormulaBeta (F1 \<or>.F2)" by simp
      hence "Comp1 (F1 \<or>.F2) \<in> H \<or> Comp2 (F1 \<or>.F2) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)
      hence "F1 \<in> H \<or> F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      thus ?thesis
      proof(rule disjE)
        assume "F1 \<in> H"
        moreover
        have "(F1, F1 \<or>. F2) \<in> measure tamano" by simp
        hence "(F1 \<in> H \<longrightarrow>  valor (IH H) F1 = Verdad)"
        using hip2 by simp
        ultimately
        have "valor (IH H) F1 = Verdad" by simp
        thus "valor (IH H) (F1 \<or>. F2) = Verdad" by (simp add: v_disyuncion_def)
        next
        assume "F2 \<in> H"
        moreover
        have "(F2, (F1 \<or>. F2)) \<in> measure tamano" by simp
        hence "F2 \<in> H \<longrightarrow>  valor (IH H) F2 =Verdad"
        using hip2 by simp
        ultimately
        have "valor (IH H) F2 = Verdad" by simp
        thus "valor (IH H) (F1 \<or>. F2) = Verdad" by (simp add: v_disyuncion_def)
      qed
    qed
  qed
  next
  show "(\<not>.(F1 \<or>. F2)) \<in> H \<longrightarrow>
  valor (IH H) (\<not>.(F1 \<or>. F2)) = Verdad"
  proof(rule impI)
    assume h2: "(\<not>.(F1  \<or>. F2)) \<in> H"
    show "valor (IH H) (\<not>.(F1  \<or>. F2)) = Verdad"
    proof -
      have "FormulaAlfa(\<not>.(F1 \<or>. F2))" by simp
      hence "Comp1 (\<not>.(F1 \<or>. F2)) \<in> H \<and> Comp2 (\<not>.(F1 \<or>. F2)) \<in> H"
      using hip1 h2 by(auto simp add: hintikkaP_def)
      hence "\<not>.F1 \<in> H \<and> \<not>.F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      hence "(\<not>.F1) \<in> H" and "(\<not>.F2) \<in> H" by auto
      moreover
      have "(\<not>.F1, F1 \<or>. F2) \<in> measure tamano" and
     "(\<not>.F2, F1 \<or>. F2) \<in> measure tamano" using ptamano
      by auto
      hence "((\<not>.F1) \<in> H \<longrightarrow> valor (IH H) (\<not>.F1) = Verdad)" and
           "((\<not>.F2) \<in> H \<longrightarrow> valor (IH H) (\<not>.F2) = Verdad)"
      using hip2 by auto
      ultimately
      have 1: "valor (IH H) (\<not>.F1) = Verdad" and
           2: "valor (IH H) (\<not>.F2) = Verdad" by auto
      have "valor (IH H) F1 = Falso" using 1 ValoresNegacion2 by auto
      moreover
      have "valor (IH H) F2 = Falso" using 2 ValoresNegacion2 by auto
      ultimately
      show  "valor (IH H) (\<not>.(F1 \<or>. F2)) = Verdad"
      by (simp add: v_disyuncion_def, simp add: v_negacion_def)
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma casoP6:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, F1  \<rightarrow>. F2) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G) = Verdad)"
shows "((F1  \<rightarrow>. F2) \<in> H \<longrightarrow> valor (IH H) (F1  \<rightarrow>. F2) = Verdad) \<and>
((\<not>.(F1  \<rightarrow>. F2)) \<in> H \<longrightarrow> valor (IH H) (\<not>.(F1  \<rightarrow>. F2)) = Verdad)"
(*<*)
proof(rule conjI impI)+
  assume h2: "(F1 \<rightarrow>.F2) \<in> H"
  show " valor (IH H) (F1 \<rightarrow>. F2) = Verdad"
  proof -
    have "FormulaBeta (F1 \<rightarrow>. F2)" by simp
    hence "Comp1(F1 \<rightarrow>. F2) \<in> H \<or> Comp2 (F1 \<rightarrow>. F2)\<in> H"
    using hip1 h2 by(auto simp add: hintikkaP_def)
    hence "(\<not>.F1) \<in> H \<or> F2 \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
    thus " valor (IH H) (F1 \<rightarrow>. F2) = Verdad"
    proof(rule disjE)
      assume "(\<not>.F1) \<in> H"
      moreover
      have "(\<not>.F1, F1  \<rightarrow>. F2) \<in> measure tamano" using ptamano by auto
      hence " (\<not>.F1) \<in> H \<longrightarrow>  valor (IH H) (\<not>.F1) = Verdad"
      using hip2 by simp
      ultimately
      have 1: "valor (IH H) (\<not>.F1) = Verdad" by simp
      hence "valor (IH H) F1 = Falso" using ValoresNegacion2 by auto
      thus "valor (IH H) (F1 \<rightarrow>. F2) = Verdad"  by(simp add: v_implicacion_def)
      next
      assume "F2 \<in> H"
      moreover
      have "(F2, F1  \<rightarrow>. F2) \<in> measure tamano" by simp
      hence "(F2 \<in> H \<longrightarrow>  valor (IH H) F2 = Verdad)"
      using hip2 by simp
      ultimately
      have "valor (IH H) F2 = Verdad" by simp
      thus "valor (IH H) (F1 \<rightarrow>. F2) = Verdad" by(simp add: v_implicacion_def)
    qed
  qed
  next
  show "(\<not>.(F1 \<rightarrow>. F2)) \<in> H \<longrightarrow>
        valor (IH H) (\<not>.(F1 \<rightarrow>. F2)) = Verdad"
  proof(rule impI)
    assume h2: "(\<not>.(F1 \<rightarrow>. F2)) \<in> H"
    show "valor (IH H) (\<not>.(F1 \<rightarrow>. F2)) = Verdad"
    proof -
      have "FormulaAlfa (\<not>.(F1 \<rightarrow>. F2))" by auto
      hence "Comp1(\<not>.(F1 \<rightarrow>. F2)) \<in> H \<and> Comp2(\<not>.(F1 \<rightarrow>. F2))\<in> H"
      using hip1 h2 by (auto simp add: hintikkaP_def)
      hence "F1 \<in> H \<and> (\<not>.F2) \<in> H" by(unfold Comp1_def, unfold Comp2_def, auto)
      moreover
      have "(F1, F1  \<rightarrow>. F2) \<in> measure tamano" and
      "(\<not>.F2, F1  \<rightarrow>. F2) \<in> measure tamano" using ptamano
      by auto
      hence "F1 \<in> H \<longrightarrow> valor (IH H) F1 = Verdad"
      and "(\<not>.F2) \<in> H \<longrightarrow> valor (IH H) (\<not>.F2) = Verdad"
      using hip2 by auto
      ultimately
      have "valor (IH H) F1 = Verdad"
      and
     "valor (IH H) (\<not>.F2) = Verdad"  by auto
      thus
     "valor (IH H) (\<not>.(F1 \<rightarrow>. F2)) = Verdad" by(simp add: v_implicacion_def)
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma casoP7:
assumes hip1: "hintikkaP H" and
hip2: "\<forall>G. (G, (\<not>.form)) \<in> measure tamano \<longrightarrow>
(G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and> ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G) = Verdad)"
shows "((\<not>.form) \<in> H \<longrightarrow> valor (IH H) (\<not>.form) = Verdad) \<and>
((\<not>.(\<not>.form)) \<in> H \<longrightarrow> valor (IH H) (\<not>.(\<not>.form)) = Verdad)"
(*<*)
proof(rule_tac conjI)
  show  "\<not>.form \<in> H \<longrightarrow> valor (IH H) (\<not>.form) = Verdad"
  proof(rule impI)
    assume h1: "(\<not>.form) \<in> H"
    moreover
    have "(form, (\<not>.form)) \<in> measure tamano" by simp
    hence "((\<not>.form) \<in> H \<longrightarrow>
           valor (IH H) (\<not>.form)= Verdad)"
    using hip2 by simp
    ultimately
    show "valor (IH H) (\<not>.form) = Verdad" using h1 by simp
  qed
  next
  show "(\<not>.\<not>.form) \<in> H \<longrightarrow> valor (IH H) (\<not>.\<not>.form) = Verdad"
  proof(rule impI)
    assume h2: "(\<not>.\<not>.form) \<in> H"
    have "\<forall>Z. (\<not>.\<not>.Z) \<in> H \<longrightarrow> Z \<in> H" using hip1
    by(unfold hintikkaP_def) blast
    hence "(\<not>.\<not>.form) \<in> H \<longrightarrow> form \<in> H" by simp
    hence "form \<in> H" using h2 by simp
    moreover
    have "(form, (\<not>.form)) \<in> measure tamano" by simp
    hence "form \<in> H \<longrightarrow> valor (IH H) form = Verdad"
    using hip2 by simp
    ultimately
    have "valor (IH H) form = Verdad" by simp
    thus  "valor (IH H) (\<not>.\<not>.form) = Verdad" using h2 by (simp add: v_negacion_def)
  qed
qed
(*>*)
text\<open>
  Usando los lemas anteriores, se tiene la formalización del teorema
  \ref{hintikkaP-model-aux}.
\<close>

theorem hintikkaP_model_aux:
  assumes hip: "hintikkaP H"
  shows "(F \<in> H \<longrightarrow>  valor (IH H) F = Verdad) \<and>
                    ((\<not>.F) \<in> H \<longrightarrow> valor (IH H) (\<not>.F) = Verdad)"
proof (rule_tac r="measure tamano" and a=F in wf_induct)
  show "wf(measure tamano)" by simp
next
  fix F
  assume hip1: "\<forall>G. (G, F) \<in> measure tamano \<longrightarrow>
                    (G \<in> H \<longrightarrow> valor (IH H) G = Verdad) \<and>
                    ((\<not>.G) \<in> H  \<longrightarrow> valor (IH H) (\<not>.G) = Verdad)"
  show "(F \<in> H \<longrightarrow> valor (IH H) F = Verdad) \<and>
        ((\<not>.F) \<in> H \<longrightarrow> valor (IH H) (\<not>.F) = Verdad)"
  proof (cases F)
    assume "F=FF"
    thus ?thesis using casoP1 hip hip1 by simp
  next
    assume "F=TT"
    thus ?thesis using casoP2 hip hip1 by auto
  next
    fix P
    assume "F = Atomo P"
    thus ?thesis using hip hip1 casoP3[of H P] by simp
  next
    fix F1  F2
    assume "F= (F1 \<and>. F2)"
    thus ?thesis using hip hip1 casoP4[of H F1 F2] by simp
  next
    fix F1 F2
    assume "F= (F1 \<or>. F2)"
    thus ?thesis using hip hip1 casoP5[of H F1 F2] by simp
  next
    fix F1 F2
    assume "F= (F1 \<rightarrow>. F2)"
    thus ?thesis using hip hip1 casoP6[of H F1 F2] by simp
  next
    fix F1
    assume "F=(\<not>.F1)"
    thus ?thesis using hip hip1 casoP7[of H F1] by simp
  qed
qed

text \<open>
  Por último, como un corolario del teorema anterior se demuestra que
  $I_H$ es un mo\-delo del conjunto de Hintikka $H$.

  \begin{corolario}\label{ModeloHintikkaPa}
  Sea $H$ un conjunto de Hintikka. Si $F\in H$ entonces $I'_H(F)=\V.$
  \end{corolario}

  \begin{demostracion}
  Es consecuencia inmediata del teorema \ref{hintikkaP-model-aux}
  \end{demostracion}

  \noindent Su formalización es:
\<close>

corollary ModeloHintikkaPa:
  assumes "hintikkaP H" and "F \<in> H"
  shows "valor (IH H) F = Verdad"
using assms hintikkaP_model_aux by auto

text \<open>
  \begin{corolario}\label{ModeloHintikkaP}
  Sea $H$ es un conjunto de Hintikka. Entonces, $I_H$ es un modelo de
  $H$.
  \end{corolario}

  \begin{demostracion}
  Es consecuencia inmediata de la definición de modelo y del corolario anterior.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

corollary ModeloHintikkaP:
  assumes "hintikkaP H"
  shows "(IH H) modelo H"
proof (unfold modelo_def)
  show "\<forall>F\<in>H. valor (IH H) F = Verdad"
  proof (rule ballI)
    fix F
    assume "F \<in> H"
    thus "valor (IH H) F = Verdad" using assms ModeloHintikkaPa  by auto
  qed
qed

text \<open>
  De esta forma, cualquier conjunto de Hintikka es satisfactible.

  \begin{corolario}\label{Hintikkasatisfacible}
  Cualquier conjunto de Hintikka es satisfactible.
  \end{corolario}

  \begin{demostracion}
  Es consecuencia inmediata de la definición de satisfactibilidad y del
  corolario \ref{ModeloHintikkaP}.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

corollary Hintikkasatisfacible:
  assumes "hintikkaP H"
  shows "satisfacible H"
using assms ModeloHintikkaP
by (unfold satisfacible_def, auto)

(*<*)
end
(*>*)
