(* header\<open> Teorema de existencia de modelos proposicionales \<close>*)

(*<*)
theory T5CCerradaP
imports T1SintaxisSemanticaP T2NotacionUniformeP
begin
(*>*)

text \<open>
  \label{cap6}
\<close>

section\<open> Teorema de Existencia de Modelos \<close>
text \<open>
  \label{consistcerradoP}
   Un método de
  demostración, utilizado por el lógico Leon Henkin, para demostrar la completitud
  de un sistema de deducción es considerar la
  afirmación contrarrecíproca, es decir, si una fórmula $F$ no es
  deducible entonces no es tautología. La prueba utiliza el siguiente
  teorema que hace referencia a la noción de {\em consistencia}.  Una
  fórmula $F$ es consistente, con respecto al cálculo de prueba
  $\vdash$, si $\nvdash \neg F$; es decir, si $\neg F$ no es deducible
  en el sistema.

  \begin{teorema}[Henkin]\label{Henkin}
  Para cualquier fórmula $F$, Si $F$ es consistente entonces $F$ tiene
  un modelo.
  \end{teorema}

  Como una consecuencia del teorema anterior podemos demostrar que
  el sistema deductivo es completo. Consideremos una fórmu\-la $F$
  que no es deducible, $\nvdash F$. Además supongamos que
  $\vdash \neg \neg F \rightarrow F$. Entonces, de la
  hipótesis $\nvdash F$ y por la regla MP tene\-mos que $\nvdash \neg \neg F$,
  es decir, $\nvdash \neg (\neg F)$. De esta forma, $\neg F$ es
  consistente. Luego, por el teorema \ref{Henkin}, $\neg F$ tiene un
  modelo. Por lo tanto, $F$ no es tautología.

  Para demostrar el teorema \ref{Henkin}, se extiende la noción de
  consistencia de una fórmu\-la a un conjunto de fórmulas.  Un conjunto
  finito de fórmulas $S = \{F_1, F_2,\dots , F_n\}$ es consistente si la
  fórmula $F_1\wedge F_2\wedge \dots \wedge F_n$ es consistente, es
  decir $\nvdash \neg(F_1\wedge F_2\wedge \dots \wedge F_n)$. Un
  conjunto arbitrario de fórmulas $S$ es consistente si cada subconjunto
  finito de $S$ es consistente.

  Un conjunto consistente de fórmulas $S$ es un {\em conjunto
  consistente maximal} si para toda fórmula $F\notin S$, $S\cup\{F\}$ no
  es consistente.  Un resultado importante sobre estos conjuntos es el
  teorema de Lindenbaum:

  \begin{teorema}[Lindenbaum]\label{Lindenbaum}
  Todo conjunto consistente $S$ puede ser extendido a un conjunto
  consistente maximal $M$.
  \end{teorema}

  El conjunto $M$ se define, a partir de $S$ y de una @{text
  "enumeración"} $\phi_0$, $\phi_1$, $\phi_2$, $\ldots$ del conjunto de
  fórmulas del lenguaje proposicional, como la unión $\bigcup_i S_i$ de
  la siguiente sucesión $S_i$ de conjuntos consistentes:
  \[
  \begin{array}{l}
    S_0 = S \\
    S_{i+1} =
     \left\{
      \begin{array}{ll}
      S_i \cup \{\phi_i\} &
        \hbox{si } S_i \cup \{\phi_i\} \hbox{ es consistente} \\
      S_i &
        \hbox{en otro caso.}
      \end{array}
     \right.
  \end{array}
  \]

  Sea $M$ un conjunto consistente maximal. Para establecer la conexión
  entre conjuntos consistentes e interpretaciones, definimos la
  siguiente interpretación $I_M$.  Sea $P$ un símbolo proposicional,
  entonces
  \newline \hspace*{1cm}
    \[ I_M(P) =
       \begin{cases}
         \V, & \text{si $P\in M$} \\
         \F, & \text{en otro caso.}
       \end{cases} \]

  Se tiene el siguiente resultado.

  \begin{teorema}\label{preHintikka}
  Si $M$ es un conjunto consistente maximal, entonces para toda fórmula
  $F$, $I'_M(F)=\V$ si y solamente si $F\in M$.
  \end{teorema}

  Como una consecuencia del teorema anterior se tiene la demostración
  del teorema \ref{Henkin}:

  \begin{demostracion}
  Sea $F$ una fórmula consistente. Por el teorema \ref{Lindenbaum},
  $\{F\}$ puede extenderse a un conjunto consistente maximal $M$. Por el
  teorema \ref{preHintikka}, $I'_M(F)=\V$ puesto que $F\in M$. Es decir,
  $F$ tiene un modelo.
  \end{demostracion}

  Utilizando el concepto abstracto de conjunto consiste y siguiendo
  las ideas anteriores, de extender un conjunto consistente de fórmulas
  $S$ a un conjunto consistente maximal $M$,
  el desarrollo central de la demostración que aparece en el texto de
  Fitting, (\cite{Fitting} página 60), es el sigui\-ente.
  \begin{itemize}
  \item Usando la noción de @{text "clausura por subconjuntos"} se
    prueba que $M$ es maximal.
  \item Usando la noción de @{text "carácter finito"} se prueba que $M$
    es consistente.
  \end{itemize}

  Además se demuestran los siguientes dos resultados.
  \begin{itemize}
  \item Al ser $M$ un conjunto maximal de carácter finito es de  @{text "Hintikka"}.
  \item Los conjuntos de Hintikka son satisfactibles.
  \end{itemize}

  Por tanto, se puede concluir que $M$ es satisfactible y, puesto que
  @{text "S \<subseteq> M"}, se tiene que $S$ también es satisfacible.
\<close>

subsection \<open> Conjuntos consistentes\<close>

text \<open>
  \label{conjuntosconsistentesP}
  En esta sección formalizamos el criterio abstracto, propuesto en
  (\cite{Fitting} página 59), para describir los conjuntos consistentes.

  \begin{definicion}\label{consistenciaP}
  Una colección de conjuntos de fórmulas $\mathcal{C}$ es una
  {\bf{propiedad de consistencia proposicional}}, si todo elemento
  $S$ de $\mathcal{C}$ verifica las siguien\-tes propiedades.
  \begin{enumerate}
  \item Para cualquier fórmula atómica $P$, $P\notin S$ o $\neg P \notin S$.
  \item $\bot\notin S$ y $\neg \top\notin S$.
  \item Si $\neg \neg F \in S$ entonces $S\cup \{F\}\in \mathcal{C}$.
  \item Si $\alpha \in S$ entonces, $S\cup\{\alpha_1,\alpha_2\}\in \mathcal{C}$.
  \item Si $\beta \in S$ entonces, $S\cup \{\beta_1\}\in \mathcal{C}$ o
    $S\cup \{\beta_2\}\in \mathcal{C}$.
  \end{enumerate}
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition consistenciaP :: "'b formula set set \<Rightarrow> bool" where
  "consistenciaP \<C> =
     (\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P. \<not> (Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S)) \<and>
     FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
     (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in>  \<C>) \<and>
     (\<forall>F. ((FormulaAlfa F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F, Comp2 F}) \<in> \<C>) \<and>
     (\<forall>F. ((FormulaBeta F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F}\<in>\<C>) \<or> (S\<union>{Comp2 F}\<in>\<C>)))"

subsection \<open> Conjuntos consistentes y clausura por subconjuntos \<close>

text \<open>
  \label{cerraduraP}
  \begin{definicion}\label{subcerrada}
  Una colección  de conjuntos $\mathcal{C}$ es {\bf{cerrada por
  subconjuntos}} si para cada $S\in\mathcal{C}$ los subconjuntos de $S$
  también son elementos de $\mathcal{C}$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition subconj_cerrada :: "'a set set \<Rightarrow> bool" where
  "subconj_cerrada \<C> = (\<forall>S \<in> \<C>. \<forall>S'. S' \<subseteq> S \<longrightarrow> S' \<in> \<C>)"

text \<open>
  En esta sección demostraremos que toda propiedad de consistencia
  proposicional $\mathcal{C}$ puede extenderse a una propiedad de
  consistencia $\mathcal{C^{+}}$ que es cerrada por subconjuntos. Para
  la demostración basta con considerar $\mathcal{C^{+}}$ igual a la
  colección de los subconjuntos de los elementos de $\mathcal{C}$,
  \[\mathcal{C^{+}}=\{S| \exists S' \in \mathcal{C} (S \subseteq
  S')\}.\] La definición en Isabelle de $\mathcal{C^{+}}$ es,
\<close>

definition clausura_subconj :: "'a set set \<Rightarrow> 'a set set" ("_⁺"[1000] 1000) where
  "\<C>⁺ = {S. \<exists>S' \<in> \<C>. S \<subseteq> S'}"

text \<open>
  \begin{teorema}\label{CerraduraSubconjuntosP}\mbox{}
  \par\noindent
  Sea $\mathcal{C}$ una colección de conjuntos. entonces,
  \begin{itemize}
  \item[(a)] $\mathcal{C} \subseteq \mathcal{C^{+}}$.
  \item[(b)] $\mathcal{C^{+}}$ es cerrada por subconjuntos.
  \item[(c)] Si $\mathcal{C}$ es una propiedad de consistencia
    proposicional entonces $\mathcal{C^{+}}$ también es una propiedad de
    consistencia proposicional.
  \end{itemize}
  \end{teorema}
\<close>

text \<open>
  \begin{demostracion}
  \begin{itemize}
  \item[(a)] Sea  $S \in \mathcal{C}$. Puesto que $S \subseteq S$ se
    tiene que $S \in \mathcal{C^{+}}$ por la definición de
    $\mathcal{C^{+}}$. Por tanto $\mathcal{C}$ está contenido en
    $\mathcal{C^{+}}$.

  \item[(b)] Supongamos que $S \in \mathcal{C^{+}}$ y sea $T\subseteq
    S$. Puesto que $S \in \mathcal{C^{+}}$, existe $S'\in \mathcal{C}$
    tal que $S \subseteq S'$ por la definición de
    $\mathcal{C^{+}}$. Luego existe $S'\in \mathcal{C}$ tal que
    $T\subseteq S'$ y, por tanto, $T\in \mathcal{C^{+}}$. Así,
    $\mathcal{C^{+}}$ es una colección cerrada por subconjuntos.

  \item[(c)] Supongamos que $\mathcal{C}$ es una propiedad de
    consistencia proposicional.  Sea $S\in \mathcal{C^{+}}$, entonces
    existe $S'\in \mathcal{C}$ tal que $S\subseteq S'$, de esto último
    mostramos que se cumplen las condiciones para que $\mathcal{C^{+}}$
    sea una propiedad de consistencia.
  \end{itemize}
  \begin{enumerate}

  \item Sea $P$ una fórmula atómica, entonces $P\notin S'$ o $\neg P
    \notin S'$ ya que $S'\in \mathcal{C}$ y $\mathcal{C}$ es una
    propiedad de consistencia. Luego, $P\notin S$ o $\neg P \notin S$
    puesto que $S\subseteq S'$.

  \item $\bot\notin S'$ y $\neg \top \notin S'$ puesto que $S'\in
    \mathcal{C}$ y $\mathcal{C}$ es una propiedad de consistencia.
    Luego, $\bot\notin S$ y $\neg \top \notin S$ puesto que $S\subseteq
    S'$.

  \item Supongamos que $\neg \neg F \in S$, entonces $\neg \neg F \in
    S'$ ya que $S\subseteq S'$.  Luego $S'\cup \{F\}\in \mathcal{C}$, ya
    que $S'\in \mathcal{C}$ y $\mathcal{C}$ es una propiedad de
    consistencia; además $S\cup \{F\}\subseteq S'\cup \{F\}$ puesto que
    $S\subseteq S'$.  Por lo tanto, por definición de $\mathcal{C^{+}}$,
    se tiene que $S\cup \{F\}\in \mathcal{C^{+}}$.

  \item Supongamos que $\alpha \in S$, entonces $\alpha \in S'$ ya que
    $S\subseteq S'$.  Luego $S'\cup \{\alpha_1,\alpha_2\} \in
    \mathcal{C}$, ya que $S'\in \mathcal{C}$ y $\mathcal{C}$ es una
    propiedad de consistencia.

  Por otro lado $S\cup \{\alpha_1, \alpha_2\}\subseteq S'\cup
  \{\alpha_1,\alpha_2\}$ ya que, $S\subseteq S'$.  Por lo tanto, por
  definición de $\mathcal{C^{+}}$, se tiene que $S\cup \{\alpha_1,
  \alpha_2\}\in \mathcal{C^{+}}$.  \item Supongamos que $\beta \in S$,
  entonces $\beta\in S'$ puesto que que $S\subseteq S'$.

  Luego, $S'\cup \{\beta_1\}\in \mathcal{C}$ o $S'\cup \{\beta_2\}\in
  \mathcal{C}$ por ser $\mathcal{C}$ una propiedad de consistencia;
  además $S\cup \{\beta_1\} \subseteq S'\cup \{\beta_1\}$ y $S\cup
  \{\beta_2\} \subseteq S'\cup \{\beta_2\}$ ya que $S\subseteq S'$. Por
  lo tanto, por definición de $\mathcal{C^{+}}$, se tiene que $S\cup
  \{\beta_1\}\in \mathcal{C^{+}}$ o $S\cup \{\beta_2\}\in
  \mathcal{C^{+}}$.
  \end{enumerate}
  \mbox{}
  \end{demostracion}

  A continuación formalizamos cada parte del teorema anterior.  La
  formali\-zación de la parte (a) es la siguiente:
\<close>

lemma cerrado_subset: "\<C> \<subseteq> \<C>⁺"
proof -
  { fix S
    assume "S \<in> \<C>"
    moreover
    have "S \<subseteq> S" by simp
    ultimately
    have "S \<in> \<C>⁺"
      by (unfold clausura_subconj_def, auto) }
  thus ?thesis by auto
qed

text \<open>
  El siguiente lema formaliza la parte (b).
\<close>

lemma cerrado_cerrado: "subconj_cerrada (\<C>⁺)"
proof -
 { fix S T
   assume "S \<in> \<C>⁺" and "T \<subseteq> S"
   obtain S1 where "S1 \<in> \<C>" and "S \<subseteq> S1" using `S \<in> \<C>⁺`
     by (unfold clausura_subconj_def, auto)
   have "T \<subseteq> S1" using `T \<subseteq> S` and `S \<subseteq> S1`  by simp
   hence "T \<in> \<C>⁺" using `S1 \<in> \<C>`
     by (unfold clausura_subconj_def, auto)}
 thus ?thesis by (unfold subconj_cerrada_def, auto)
qed

text \<open>
  Los siguientes lemas corresponden a la formalización de los 5 casos de
  la parte (c) del teorema anterior.
\<close>

lemma condiconsisP1:
  assumes "consistenciaP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"
  shows "(\<forall>P. \<not>(Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S))"
(*<*)
proof (rule allI)+
  fix P
  show "\<not>(Atomo P  \<in> S \<and> (\<not>.Atomo P) \<in> S)"
  proof -
    have "\<not>(Atomo P \<in> T \<and> (\<not>.Atomo P) \<in> T)"
      using `consistenciaP \<C>` and `T \<in> \<C>`
      by(simp add: consistenciaP_def)
    thus "\<not>(Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S)" using `S \<subseteq> T` by auto
  qed
qed
(*>*)
text\<open> \<close>
lemma condiconsisP2:
  assumes "consistenciaP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"
  shows "FF \<notin> S \<and> (\<not>.TT)\<notin> S"
(*<*)
proof -
  have "FF \<notin> T \<and> (\<not>.TT)\<notin> T"
    using `consistenciaP \<C>` and `T \<in> \<C>`
    by(simp add: consistenciaP_def)
  thus "FF \<notin> S \<and> (\<not>.TT)\<notin> S" using `S \<subseteq> T` by auto
qed
(*>*)
text\<open> \<close>
lemma condiconsisP3:
  assumes "consistenciaP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁺"
proof(rule allI)
(*<*)
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁺"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    hence "(\<not>.\<not>.F) \<in> T" using `S \<subseteq> T` by auto
    hence "T \<union> {F} \<in> \<C>" using `consistenciaP \<C>` and `T \<in> \<C>`
      by(simp add: consistenciaP_def)
    moreover
    have "S \<union> {F} \<subseteq>  T \<union> {F}" using `S \<subseteq> T` by auto
    ultimately
    show "S \<union> {F} \<in> \<C>⁺"
      by (auto simp add: clausura_subconj_def)
  qed
qed
(*>*)
text\<open> \<close>
lemma condiconsisP4:
  assumes "consistenciaP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"
  shows "\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁺"
(*<*)
proof (rule allI)
  fix F
  show "((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁺"
  proof (rule impI)
    assume "((FormulaAlfa F) \<and> F \<in> S)"
    hence "FormulaAlfa F" and  "F \<in> T" using `S \<subseteq> T` by auto
    hence  "T \<union> {Comp1 F, Comp2 F} \<in> \<C>"
      using `consistenciaP \<C>` and `FormulaAlfa F` and `T \<in> \<C>`
      by (auto simp add: consistenciaP_def)
    moreover
    have "S \<union> {Comp1 F, Comp2 F} \<subseteq> T \<union> {Comp1 F, Comp2 F}"
      using `S \<subseteq> T` by auto
    ultimately
    show  "S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁺"
      by (auto simp add: clausura_subconj_def)
  qed
qed
(*>*)
text\<open>\<close>
lemma condiconsisP5:
  assumes "consistenciaP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"
  shows "(\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow>
              (S \<union> {Comp1 F} \<in> \<C>⁺) \<or> (S \<union> {Comp2 F} \<in> \<C>⁺))"
(*<*)
proof (rule allI)
  fix F
  show "((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁺ \<or> S \<union> {Comp2 F} \<in> \<C>⁺"
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S"
    hence "FormulaBeta F" and "F \<in> T" using `S \<subseteq> T` by auto
    hence "T \<union> {Comp1 F} \<in> \<C> \<or> T \<union> {Comp2 F} \<in> \<C>"
      using `consistenciaP \<C>` and `FormulaBeta F` and `T \<in> \<C>`
      by(simp add: consistenciaP_def)
    moreover
    have "S \<union> {Comp1 F} \<subseteq> T \<union> {Comp1 F}" and "S \<union> {Comp2 F} \<subseteq> T \<union> {Comp2 F}"
      using `S \<subseteq> T` by auto
    ultimately
    show "S \<union> {Comp1 F} \<in> \<C>⁺ \<or> S \<union> {Comp2 F} \<in> \<C>⁺"
      by(auto simp add: clausura_subconj_def)
  qed
qed
(*>*)
text \<open>
  Por último, la formalización de la parte (c) del teorema
  \ref{CerraduraSubconjuntosP} es la siguiente:
\<close>

theorem cerrado_consistenciaP:
  assumes hip1: "consistenciaP \<C>"
  shows "consistenciaP (\<C>⁺)"
proof -
  { fix S
    assume "S \<in> \<C>⁺"
    hence "\<exists>T\<in>\<C>. S \<subseteq> T" by(simp add: clausura_subconj_def)
    then obtain T where hip2: "T \<in> \<C>" and hip3: "S \<subseteq> T" by auto
    have "(\<forall>P. \<not> (Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S)) \<and>
               FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
               (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁺) \<and>
               (\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow>
                    (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁺) \<and>
               (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow>
                    (S \<union> {Comp1 F} \<in> \<C>⁺) \<or> (S \<union> {Comp2 F} \<in> \<C>⁺))"
      using
        condiconsisP1[OF hip1 hip2 hip3]  condiconsisP2[OF hip1 hip2 hip3]
        condiconsisP3[OF hip1 hip2 hip3]  condiconsisP4[OF hip1 hip2 hip3]
        condiconsisP5[OF hip1 hip2 hip3]
      by blast}
  thus ?thesis by (simp add: consistenciaP_def)
qed

(*<*)
end
(*>*)
