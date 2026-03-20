
theory TeoriaCompacidad2
(*<*)
  imports Main
 "/Users/fabian/Dropbox/Teorias1/ExistenciaModelos/ExistenciaModeloP"
begin
(*>*)
section \<open> Teorema de Compacidad \<close>

text\<open>
Se formaliza en Isabelle/HOL, utilizando la formalización del Teorema de Existencia de Modelos,
 el Teorema de Compacidad para la Lógica Proposicional:
\par
Sean $L$ un lenguaje proposicional enumerable y $S$ un
  conjunto de fórmulas proposicionales. Si todo subconjunto finito de
  $S$ es satisfacible, entonces $S$ es satisfacible.
\<close>
lemma NosatisfacibleAtom:
  shows "\<not>(satisfacible {F, \<not>.F})"
proof (rule notI)
  assume hip: "satisfacible {F, \<not>.F}"
  show "False"
  proof -
    have  "\<exists>I. I modelo {F, \<not>.F}" using hip by(unfold satisfacible_def, auto)
    then obtain I where I: "valor I F = Verdad"
      and "valor I (\<not>.F) = Verdad"
      by(unfold modelo_def, auto)
    thus "False" by(auto simp add: v_negacion_def)
  qed
qed

lemma comp1:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A"
  shows "(\<forall>P. \<not> (Atom P \<in> W \<and> (\<not>. Atom P) \<in> W))"
proof (rule allI notI)+
  fix P
  assume h1: "Atom P \<in> W \<and> (\<not>.Atom P) \<in> W"
  show "False"
  proof -
    have "{Atom P, (\<not>.Atom P)} \<subseteq> W" using h1 by simp
    moreover
    have "finite {Atom P, (\<not>.Atom P)}" by simp
    ultimately
    have "{Atom P, (\<not>.Atom P)} \<subseteq> W \<and> finite {Atom P, (\<not>.Atom P)}" by simp
    moreover
    have "({Atom P, (\<not>.Atom P)}\<subseteq> W \<and> finite {Atom P, (\<not>.Atom P)}) \<longrightarrow>
          satisfacible {Atom P, (\<not>.Atom P)}"
      using assms by(rule_tac x = "{Atom P, (\<not>.Atom P)}" in allE, auto)
    ultimately
    have "satisfacible {Atom P, (\<not>.Atom P)}" by simp
    thus "False" using NosatisfacibleAtom by auto
  qed
qed

lemma NosatisfacibleFF:
  shows "\<not> (satisfacible {FF})"
proof -
  have "\<forall> I. valor I FF = Falso" by simp
  hence "\<forall> I. \<not> (I modelo {FF})"  by(unfold modelo_def, auto)
  thus ?thesis by(unfold satisfacible_def, auto)
qed

lemma comp2:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A"
  shows "FF \<notin> W"
proof (rule notI)
  assume hip: "FF \<in> W"
  show "False"
  proof -
    have "{FF} \<subseteq> W" using hip by simp
    moreover
    have "finite {FF}" by simp
    ultimately
    have "{FF} \<subseteq> W \<and> finite {FF}" by simp
    moreover
    have "({FF::'b formula} \<subseteq> W \<and> finite {FF}) \<longrightarrow>
          satisfacible {FF::'b formula}"
      using assms by(rule_tac x = "{FF::'b formula}" in allE, auto)
    ultimately
    have "satisfacible {FF::'b formula}" by simp
    thus "False" using NosatisfacibleFF by auto
  qed
qed

lemma NosatisfacibleFFa:
  shows "\<not> (satisfacible {\<not>.TT})"
proof -
  have "\<forall> I. valor I TT = Verdad" by simp
  have "\<forall> I. valor I (\<not>.TT) = Falso" by(auto simp add: v_negacion_def)
  hence "\<forall> I. \<not> (I modelo {\<not>.TT})"  by(unfold modelo_def, auto)
  thus ?thesis by(unfold satisfacible_def, auto)
qed

lemma comp3:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A"
  shows "\<not>.TT \<notin> W"
proof (rule notI)
  assume hip: "\<not>.TT \<in> W"
  show "False"
  proof -
    have "{\<not>.TT} \<subseteq> W" using hip by simp
    moreover
    have "finite {\<not>.TT}" by simp
    ultimately
    have "{\<not>.TT} \<subseteq> W \<and> finite {\<not>.TT}" by simp
    moreover
    have "({\<not>.TT::'b formula} \<subseteq> W \<and> finite {\<not>.TT}) \<longrightarrow>
          satisfacible {\<not>.TT::'b formula}"
      using assms by(rule_tac x = "{\<not>.TT::'b formula}" in allE, auto)
    ultimately
    have "satisfacible {\<not>.TT::'b formula}" by simp
    thus "False" using NosatisfacibleFFa by auto
  qed
qed

lemma SubSatis:
  assumes hip1: "satisfacible S" and hip2: "S'\<subseteq> S"
  shows "satisfacible S'"
proof -
  have "\<exists>I. \<forall> F \<in> S. valor I F = Verdad" using hip1
    by (unfold satisfacible_def, unfold modelo_def, auto)
  hence "\<exists>I. \<forall> F \<in> S'. valor I F = Verdad" using hip2 by auto
  thus ?thesis by(unfold satisfacible_def, unfold modelo_def, auto)
qed
text\<open> \<close>
lemma satisfacibleUnion1:
  assumes "satisfacible (A \<union> {\<not>.\<not>.F})"
  shows "satisfacible (A \<union> {F})"
proof -
  have "\<exists>I. \<forall> G \<in> (A \<union> {\<not>.\<not>.F}). valor I G = Verdad"
    using assms by(unfold satisfacible_def, unfold modelo_def, auto)
  then obtain I where I: "\<forall> G \<in> (A \<union> {\<not>.\<not>.F}). valor I G = Verdad"
    by auto
  hence 1: "\<forall> G \<in> A. valor I G = Verdad"
    and 2: "valor I (\<not>.\<not>.F) = Verdad"
    by auto
  have "tipoFormula (\<not>.\<not>.F) = NoNo" by auto
  hence "valor I  F = Verdad" using EquivNoNoComp[of "\<not>.\<not>.F"] 2
    by (unfold equivalentes_def, unfold Comp1_def, auto)
  hence "\<forall> G \<in> A \<union> {F}. valor I G = Verdad" using 1 by auto
  thus "satisfacible (A \<union> {F})"
    by(unfold satisfacible_def, unfold modelo_def, auto)
qed

lemma comp4:
  assumes hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A"
  and hip2: "\<not>.\<not>.F \<in> W"
  shows "\<forall> (A::'b formula set). (A\<subseteq> W \<union> {F} \<and> finite A) \<longrightarrow> satisfacible A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A \<subseteq> W \<union> {F} \<and> finite A"
  show "satisfacible A"
  proof -
    have "A-{F} \<subseteq> W \<and> finite (A-{F})" using hip by auto
    hence "(A-{F}) \<union> {\<not>.\<not>.F} \<subseteq> W \<and> finite ((A-{F}) \<union> {\<not>.\<not>.F})"
      using hip2 by auto
    hence "satisfacible ((A-{F}) \<union> {\<not>.\<not>.F})" using hip1 by auto
    hence "satisfacible ((A-{F}) \<union> {F})" using  satisfacibleUnion1 by blast
    moreover
    have "A\<subseteq> (A-{F}) \<union> {F}" by auto
    ultimately
    show "satisfacible A" using SubSatis by auto
  qed
qed

lemma satisfacibleUnion2:
  assumes hip1: "FormulaAlfa F" and hip2: "satisfacible (A \<union> {F})"
  shows "satisfacible (A \<union> {Comp1 F,Comp2 F})"
proof -
  have "\<exists>I.\<forall> G \<in> A \<union> {F}. valor I G = Verdad"
    using hip2 by(unfold satisfacible_def, unfold modelo_def, auto)
  then obtain I where I:  "\<forall> G \<in> A \<union> {F}. valor I G = Verdad" by auto
  hence 1: "\<forall> G \<in> A. valor I G = Verdad" and 2: "valor I F = Verdad" by auto
  have "tipoFormula F = Alfa" using hip1 noAlfaBeta noAlfaNoNo by auto
  hence "equivalentes F (Comp1 F \<and>. Comp2 F)"
    using 2 EquivAlfaComp[of F] by auto
  hence  "valor I (Comp1 F \<and>. Comp2 F) = Verdad"
    using 2 by( unfold equivalentes_def, auto)
  hence "valor I (Comp1 F) = Verdad \<and> valor I (Comp2 F) = Verdad"
    using ValoresConjuncion by auto
  hence "\<forall> G \<in> A \<union> {Comp1 F, Comp2 F} . valor I G = Verdad" using 1 by auto
  thus "satisfacible (A \<union> {Comp1 F,Comp2 F})"
    by (unfold satisfacible_def, unfold modelo_def, auto)
qed

lemma comp5:
  assumes hip0: "FormulaAlfa F"
  and hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A"
  and hip2: "F \<in> W"
  shows "\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F, Comp2 F} \<and> finite A) \<longrightarrow>
  satisfacible A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A \<subseteq> W \<union> {Comp1 F, Comp2 F} \<and> finite A"
  show "satisfacible A"
  proof -
    have "A-{Comp1 F, Comp2 F} \<subseteq> W \<and> finite (A-{Comp1 F, Comp2 F})"
      using hip by auto
    hence "(A-{Comp1 F, Comp2 F}) \<union> {F} \<subseteq> W \<and>
           finite ((A-{Comp1 F, Comp2 F}) \<union> {F})"
      using hip2 by auto
    hence "satisfacible ((A-{Comp1 F, Comp2 F}) \<union> {F})"
      using hip1 by auto
    hence "satisfacible ((A-{Comp1 F, Comp2 F}) \<union> {Comp1 F, Comp2 F})"
      using hip0 satisfacibleUnion2 by auto
    moreover
    have  "A \<subseteq> (A-{Comp1 F, Comp2 F}) \<union> {Comp1 F, Comp2 F}" by auto
    ultimately
    show "satisfacible A" using SubSatis by auto
  qed
qed

lemma satisfacibleUnion3:
  assumes hip1: "FormulaBeta F" and hip2: "satisfacible (A \<union> {F})"
  shows "satisfacible (A \<union> {Comp1 F}) \<or> satisfacible (A \<union> {Comp2 F})"
proof -
  obtain I where I: "\<forall>G \<in> (A \<union> {F}). valor I G = Verdad"
  using hip2 by(unfold satisfacible_def, unfold modelo_def, auto)
  hence S1: "\<forall>G \<in> A. valor I G = Verdad"
    and S2: " valor I F = Verdad"
    by auto
  have V: "valor I (Comp1 F) = Verdad \<or> valor I (Comp2 F) = Verdad"
    using hip1 S2 EquivBetaComp[of F] ValoresDisyuncion
    by (unfold equivalentes_def, auto)
  have "((\<forall>G \<in> A. valor I G = Verdad) \<and> valor I (Comp1 F) = Verdad) \<or>
        ((\<forall>G \<in> A. valor I G = Verdad) \<and> valor I (Comp2 F) = Verdad)"
    using V
  proof (rule disjE)
    assume "valor I (Comp1 F) = Verdad"
    hence "(\<forall>G \<in> A. valor I G = Verdad) \<and> valor I (Comp1 F) = Verdad"
      using S1 by auto
    thus ?thesis by simp
  next
    assume "valor I (Comp2 F) = Verdad"
    hence "(\<forall>G \<in> A. valor I G = Verdad) \<and> valor I (Comp2 F) = Verdad"
      using S1 by auto
    thus ?thesis by simp
  qed
  hence "(\<forall>G \<in> A \<union> {Comp1 F}. valor I G = Verdad) \<or>
         (\<forall>G \<in> A \<union> {Comp2 F}. valor I G = Verdad)"
    by auto
  hence "(\<exists>I.\<forall>G \<in> A \<union> {Comp1 F}. valor I G = Verdad) \<or>
         (\<exists>I.\<forall>G \<in> A \<union> {Comp2 F}. valor I G = Verdad)"
    by auto
  thus "satisfacible (A \<union> {Comp1 F}) \<or> satisfacible (A \<union> {Comp2 F})"
  by (unfold satisfacible_def, unfold modelo_def, auto)
qed

lemma comp6:
  assumes hip0: "FormulaBeta F"
  and hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A"
  and hip2: "F \<in> W"
  shows "(\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F} \<and> finite A) \<longrightarrow>
  satisfacible A) \<or>
  (\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp2 F} \<and> finite A) \<longrightarrow>
  satisfacible A)"
proof -
  { assume hip3:"\<not>((\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F} \<and> finite A) \<longrightarrow>
    satisfacible A) \<or>
    (\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp2 F} \<and> finite A) \<longrightarrow>
    satisfacible A))"
    have "False"
    proof -
      obtain A B where A1: "A \<subseteq> W \<union> {Comp1 F}"
        and A2: "finite A"
        and A3:" \<not> satisfacible A"
        and B1: "B \<subseteq> W \<union> {Comp2 F}"
        and B2: "finite B"
        and B3: "\<not> satisfacible B"
        using hip3 by auto
      have a1: "A - {Comp1 F} \<subseteq> W"
        and a2: "finite (A - {Comp1 F})"
        using A1 and A2 by auto
      hence "satisfacible (A - {Comp1 F})" using hip1 by simp
      have b1: "B - {Comp2 F} \<subseteq> W"
        and b2: "finite (B - {Comp2 F})"
        using B1 and B2 by auto
      hence "satisfacible (B - {Comp2 F})" using hip1 by simp
      moreover
      have "(A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F} \<subseteq> W"
        and "finite ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F})"
        using a1 a2 b1 b2 hip2 by auto
      hence "satisfacible ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F})"
        using hip1 by simp
      hence "satisfacible ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp1 F})
      \<or> satisfacible ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp2 F})"
        using hip0 satisfacibleUnion3 by auto
      moreover
      have "A \<subseteq> (A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp1 F}"
        and "B \<subseteq> (A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp2 F}"
        by auto
      ultimately
      have "satisfacible A \<or> satisfacible B" using SubSatis by auto
      thus "False" using A3 B3 by simp
    qed }
  thus ?thesis by auto
qed

lemma ConsistenciaCompacidad:
  shows "consistenciaP{W::'b formula set. \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow>
  satisfacible A}"
proof (unfold consistenciaP_def, rule allI, rule impI)
  let ?C = "{W::'b formula set.  \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A}"
  fix W ::" 'b formula set"
  assume "W \<in> ?C"
  hence  hip: "\<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A" by simp
  show "(\<forall>P. \<not> (Atomo P \<in> W \<and> (\<not>.Atomo P ) \<in> W)) \<and>
        FF \<notin> W \<and>
        \<not>.TT \<notin> W \<and>
        (\<forall>F. \<not>.\<not>.F \<in> W \<longrightarrow> W \<union> {F} \<in> ?C) \<and>
        (\<forall>F. (FormulaAlfa F) \<and> F \<in> W \<longrightarrow>
        (W \<union>  {Comp1 F, Comp2 F} \<in> ?C)) \<and>
        (\<forall>F. (FormulaBeta F) \<and> F \<in> W \<longrightarrow>
        (W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C))"
  proof -
    have "(\<forall>P. \<not> (Atomo P \<in> W \<and> (\<not>. Atomo P) \<in> W))"
      using hip  comp1 by simp
    moreover
    have "FF \<notin> W" using hip comp2 by auto
    moreover
    have "\<not>. TT \<notin> W" using hip comp3 by auto
    moreover
    have "\<forall>F. (\<not>.\<not>.F) \<in> W \<longrightarrow> W \<union> {F} \<in> ?C"
    proof (rule allI impI)+
      fix F
      assume hip1: "\<not>.\<not>.F \<in> W"
      show "W \<union> {F} \<in> ?C" using hip hip1 comp4 by simp
    qed
    moreover
    have
    "\<forall>F. (FormulaAlfa F) \<and> F \<in> W \<longrightarrow> (W \<union>  {Comp1 F, Comp2 F} \<in> ?C)"
    proof (rule allI impI)+
      fix F
      assume "FormulaAlfa F \<and> F \<in> W"
      thus "W \<union> {Comp1 F, Comp2 F} \<in> ?C" using hip comp5[of F] by blast
    qed
    moreover
    have "\<forall>F. (FormulaBeta F) \<and> F \<in> W \<longrightarrow>
              (W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C)"
    proof (rule allI impI)+
      fix F
      assume "(FormulaBeta F) \<and> F \<in> W"
      thus "W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C"
        using hip comp6[of F] by blast
    qed
    ultimately
    show ?thesis by auto
  qed
qed

theorem TeoremaCompacidad1:
  assumes hip1: "\<exists>g. enumeracion (g:: nat \<Rightarrow> 'b formula)"
  and hip2: "\<forall>A. (A \<subseteq> (S:: 'b formula set) \<and> finite A) \<longrightarrow> satisfacible A"
  shows "satisfacible S"
proof -
  let ?C = "{W:: 'b formula set.  \<forall>A. (A \<subseteq> W \<and> finite A) \<longrightarrow> satisfacible A}"
  have "consistenciaP ?C"
    using ConsistenciaCompacidad by simp
  moreover
  have "S \<in> ?C" using hip2 by simp
  ultimately
  show "satisfacible S" using  hip1 and TeoremaExistenciaModelos by auto
qed

corollary TeoremaCompacidad2:
  assumes "\<forall>A. (A \<subseteq> (S:: nat formula set) \<and> finite A) \<longrightarrow> satisfacible A"
  shows "satisfacible S"
using assms and EnumeracionFormulasNat and TeoremaCompacidad1
by auto

(*<*)
end
(*>*)
