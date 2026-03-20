(*<*)
theory T10MaximalHintikkaP
imports T8TeoriaHintikkaP
begin
(*>*)

subsection \<open> Conjuntos maximales y conjuntos de Hintikka\<close>

text \<open>
  \label{maximalhintikka}

  En esta sección mostramos que si $\mathcal {C}$ es una propiedad de
  consistencia proposicional que además es cerrada por subconjuntos, $M$
  es un conjunto maximal de $\mathcal{C}$ y $M$ pertenence a
  $\mathcal{C}$ entonces, $M$ es un conjunto de Hintikka.

  \begin{teorema}\label{MaximalHintikkaP}
  Sea $\mathcal{C}$ una colección de conjuntos de fórmulas tal que,
  \begin{itemize}
  \item (hip1) $\mathcal{C}$ es una propiedad de consistencia proposicional.
  \item (hip2) $M$ es un elemento maximal de $\mathcal{C}$.
  \item (hip3) $M\in \mathcal{C}$.
  \end{itemize}
  Entonces $M$ es un conjunto de Hintikka.
  \end{teorema}

  \begin{demostracion}

  A continuación mostramos que $M$ cumple las propiedades que definen un
  conjunto de Hintikka (definición \ref{DefhintikkaP}).  Las propiedades
  (1) y (2) se cumplen por las hipótesis $(hip1)$ y $(hip3)$; las
  propiedades (3) a (5) se demuestran usando las hipótesis $(hip1)$,
  $(hip2)$ y $(hip3)$:

  3. Supongamos que $\neg \neg F \in M$, hay que demostrar que $F \in
  M$. Tenemos que, si $\neg \neg F \in M$ entonces $M\cup \{F\} \in
  \mathcal{C}$, puesto que $\mathcal{C}$ es una propiedad de
  consistencia. También se tiene que para cualquier $S'\in
  \mathcal{C}$, si $M\subseteq S'$ entonces $M = S'$, puesto que $M$ es
  un elemento maximal de $\mathcal{C}$.

  De lo anterior y puesto que $M\subseteq M\cup \{F\}$ tenemos que $M =
  M\cup \{F\}$, y por lo tanto, $F \in M$.

  4. Supongamos que $\alpha \in M$.  Hay que demostrar que $\alpha_1 \in
  M$ y $\alpha_2 \in M$.  Tene\-mos que, si $\alpha \in M$ entonces $M\cup
  \{\alpha_1, \alpha_2\}\in \mathcal{C}$, ya que $\mathcal{C}$ es
  propiedad de consistencia.  También se tiene que para cualquier $S'\in
  \mathcal{C}$, si $M\subseteq S'$ entonces $M = S'$, puesto que $M$ es
  un elemento maximal de $\mathcal{C}$.

  De lo anterior y puesto que $M\subseteq M\cup \{\alpha_1, \alpha_2\}$
  tenemos que, $M = M\cup \{\alpha_1, \alpha_2\}$. Luego $\alpha_1 \in
  M$ y $\alpha_2 \in M$.

  5. Supongamos que $\beta\in M$.  Hay que demostrar que $\beta_1 \in M$
  o $\beta_2 \in M$.  Puesto que $\mathcal{C}$ es una propiedad de
  consistencia tenemos que, si $\beta \in M$ entonces, $M\cup
  \{\beta_1\}\in \mathcal{C}$ o $M\cup \{\beta_2\}\in \mathcal{C}$.  A
  partir de la anterior disyunción demostramos por el método de
  eliminación de la disyunción que, $\beta_1\in M$ o $\beta_2\in M$.

  (a) Supongamos que $M\cup \{\beta_1\}\in \mathcal{C}$.  Puesto que $M$
  es un elemento maximal de $\mathcal{C}$ tenemos que para cualquier
  $S'\in \mathcal{C}$, si $M\subseteq S'$ entonces $M = S'$.  De lo
  anterior y puesto que $M\subseteq M\cup \{\beta_1\}$ tenemos que, $M =
  M\cup \{\beta_1\}$.  Luego $\beta_1\in M$, y por lo tanto, $\beta_1\in
  M$ o $\beta_2\in M$.

  (b) Supongamos que $M\cup \{\beta_2\}\in \mathcal{C}$. La demostración
  es igual que la del caso anterior.
  \end{demostracion}

  Los siguientes lemas corresponden a la formalización de cada una de
  las partes del teorema anterior.
\<close>

lemma exten_hintikkaP1:
  assumes  hip1: "consistenciaP \<C>" and hip2: "M \<in> \<C>"
  shows   "\<forall>p. \<not> (Atomo p \<in> M \<and> (\<not>.Atomo p) \<in> M)"
(*<*)
proof -
  show ?thesis using hip1 hip2 by(unfold consistenciaP_def) simp
qed
(*>*)

text \<open> \<close>

lemma exten_hintikkaP2:
  assumes hip1: "consistenciaP \<C>" and hip2: "M \<in> \<C>"
  shows "FF \<notin> M"
(*<*)
proof -
  show ?thesis using hip1 hip2 by(unfold consistenciaP_def) simp
qed
(*>*)

text \<open> \<close>

lemma exten_hintikkaP3:
  assumes  hip1: "consistenciaP \<C>" and hip2: "M \<in> \<C>"
  shows "(\<not>.TT) \<notin> M"
(*<*)
proof -
  show ?thesis using hip1 hip2 by(unfold consistenciaP_def) simp
qed
(*>*)

text \<open> \<close>

lemma exten_hintikkaP4:
  assumes  hip1: "consistenciaP \<C>" and hip2: "maximal M \<C>" and hip3: "M \<in> \<C>"
  shows "\<forall>F. (\<not>.\<not>.F) \<in> M \<longrightarrow> F \<in> M"
(*<*)
proof (rule allI impI)+
  fix F
  assume h1: "(\<not>.\<not>.F) \<in> M"
  show "F \<in> M"
  proof -
    have "(\<not>.\<not>.F) \<in> M \<longrightarrow> M \<union> {F} \<in> \<C>"
      using hip1 hip3 by (unfold consistenciaP_def) simp
    hence "M \<union> {F} \<in> \<C>" using h1 by simp
    moreover
    have  "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
    moreover
    have "M \<subseteq> M \<union> {F}" by auto
    ultimately
    have "M = M \<union> {F}" by auto
    thus "F \<in> M" by auto
  qed
qed
(*>*)

text \<open> \<close>

lemma exten_hintikkaP5:
  assumes hip1: "consistenciaP \<C>" and hip2: "maximal M \<C>" and hip3: "M \<in> \<C>"
  shows "\<forall>F. (FormulaAlfa F) \<and> F \<in> M \<longrightarrow> (Comp1 F \<in> M \<and> Comp2 F \<in> M)"
(*<*)
proof (rule allI impI)+
  fix F
  assume h1: "(FormulaAlfa F) \<and> F \<in> M"
  show "Comp1 F \<in> M \<and> Comp2 F \<in> M"
  proof -
    have "(FormulaAlfa F) \<and> F \<in> M \<longrightarrow> M \<union> {Comp1 F, Comp2 F} \<in> \<C>"
      using hip1 hip3 by (unfold consistenciaP_def) simp
    hence  "M \<union> {Comp1 F, Comp2 F} \<in> \<C>" using h1 by simp
    moreover
    have "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
    moreover
    have "M \<subseteq> M \<union> {Comp1 F, Comp2 F}" by auto
    ultimately
    have "M = M \<union> {Comp1 F, Comp2 F}"  by simp
    thus "Comp1 F \<in> M \<and> Comp2 F \<in> M" by auto
  qed
qed
(*>*)

text \<open> \<close>

lemma exten_hintikkaP6:
  assumes hip1: "consistenciaP \<C>" and hip2: "maximal M \<C>" and  hip3: "M \<in> \<C>"
  shows "\<forall>F. (FormulaBeta F) \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<or> Comp2 F \<in> M"
(*<*)
proof (rule allI impI)+
  fix F
  assume h1: "(FormulaBeta F) \<and> F \<in> M"
  show "Comp1 F \<in> M \<or> Comp2 F \<in> M"
  proof -
    have "(FormulaBeta F) \<and> F \<in> M \<longrightarrow> M \<union> {Comp1 F} \<in> \<C> \<or> M \<union> {Comp2 F} \<in> \<C>"
      using hip1 hip3 by (unfold consistenciaP_def) simp
    hence  "M \<union> {Comp1 F} \<in> \<C> \<or> M \<union> {Comp2 F} \<in> \<C>" using h1 by simp
    thus ?thesis
    proof (rule disjE)
      assume "M \<union> {Comp1 F} \<in> \<C>"
      moreover
      have "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
      moreover
      have "M \<subseteq> M \<union> {Comp1 F}" by auto
      ultimately
      have "M = M \<union> {Comp1 F}" by simp
      hence "Comp1 F \<in> M" by auto
      thus "Comp1 F \<in> M \<or> Comp2 F \<in> M" by simp
    next
      assume "M \<union> {Comp2 F} \<in> \<C>"
      moreover
      have "\<forall>M'\<in>\<C>. M \<subseteq> M' \<longrightarrow> M = M'" using hip2 by (unfold maximal_def)
      moreover
      have "M \<subseteq> M \<union> {Comp2 F}" by auto
      ultimately
      have "M = M \<union> {Comp2 F}" by simp
      hence "Comp2 F \<in> M" by auto
      thus "Comp1 F \<in> M \<or> Comp2 F \<in> M" by simp
    qed
  qed
qed
(*>*)

text \<open>
  Por último, tenemos la formalización del teorema
  \ref{MaximalHintikkaP}.
\<close>

theorem MaximalHintikkaP:
  assumes hip1: "consistenciaP \<C>" and hip2: "maximal M \<C>" and  hip3: "M \<in> \<C>"
  shows "hintikkaP M"
proof (unfold hintikkaP_def)
  show "(\<forall>P. \<not> (Atomo P \<in> M \<and> \<not>.Atomo P \<in> M)) \<and>
        FF \<notin> M \<and>
        \<not>.TT \<notin> M \<and>
        (\<forall>F. \<not>.\<not>.F \<in> M \<longrightarrow> F \<in> M) \<and>
        (\<forall>F. FormulaAlfa F \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<and> Comp2 F \<in> M) \<and>
        (\<forall>F. FormulaBeta F \<and> F \<in> M \<longrightarrow> Comp1 F \<in> M \<or> Comp2 F \<in> M)"
    using exten_hintikkaP1[OF hip1 hip3]
          exten_hintikkaP2[OF hip1 hip3]
          exten_hintikkaP3[OF hip1 hip3]
          exten_hintikkaP4[OF hip1 hip2 hip3]
          exten_hintikkaP5[OF hip1 hip2 hip3]
          exten_hintikkaP6[OF hip1 hip2 hip3]
    by blast
qed

(*<*)
end
(*<*)
