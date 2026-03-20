(*<*)
theory TeoriaColoracion
imports Main TeoriaCompacidad2
begin
(*>*)
section \<open> Anexo 2. Teoría Coloración \<close>

text\<open>
Se formaliza en Isabelle/HOL, utilizando la formalización del Teorema de Compacidad para la Lógica Proposicional, el siguiente teorema:
\par
Un grafo $G$ infinito enumerable es $k$-colorable si todo subgrafo finito de $G$ es $k$-colorable.
\<close>


type_synonym 'v digrafo =  "('v set) \<times> (('v \<times> 'v) set)"

abbreviation vert :: "'v digrafo \<Rightarrow> 'v set"  ("V[_]" [80] 80) where
"V[G]  \<equiv> fst G"

abbreviation arc :: "'v digrafo \<Rightarrow> ('v \<times> 'v) set" ("E[_]" [80] 80) where
  "E[G] \<equiv> snd G"

definition es_grafo :: "'v digrafo \<Rightarrow> bool" where
  "es_grafo G \<equiv> \<forall> u v. (u,v) \<in> E[G] \<longrightarrow> u \<in> V[G] \<and> v \<in> V[G] \<and> u \<noteq> v"

definition es_subgrafo_inducido :: "'v digrafo \<Rightarrow>'v digrafo \<Rightarrow> bool" where
  "es_subgrafo_inducido H G \<equiv>
  (V[H] \<subseteq> V[G]) \<and> E[H] = E[G] \<inter> ((V[H]) \<times> (V[H]))"

lemma
  assumes "es_grafo G" and "es_subgrafo_inducido H G"
  shows "es_grafo H"
proof(unfold es_grafo_def)
  show "\<forall>u v. (u, v) \<in> E[H] \<longrightarrow> u \<in> V[H] \<and> v \<in> V[H] \<and> u \<noteq> v"
  proof((rule allI)+, rule impI)
    fix u v
    assume "(u, v) \<in> E[H]"
    show  "u \<in> V[H] \<and> v \<in> V[H] \<and> u \<noteq> v"
    proof-
      have  "(u, v) \<in> E[G] \<inter> (V[H]) \<times> (V[H])" using `(u, v) \<in> E[H]` assms(2)
        by(unfold es_subgrafo_inducido_def,auto)
      hence 1:  "(u, v) \<in> E[G]" and 2: "u \<in> V[H] \<and> v \<in> V[H]"  by auto
      have "u \<noteq> v" using 1  `es_grafo G`  by(unfold es_grafo_def,auto)
      thus  "u \<in> V[H] \<and> v \<in> V[H] \<and> u \<noteq> v" using 2 by auto
    qed
  qed
qed

definition grafo_finito :: "'v digrafo \<Rightarrow> bool"  where
  "grafo_finito G \<equiv> finite (V[G]) \<and> finite (E[G])"

abbreviation grafo_infinito :: "'v digrafo \<Rightarrow> bool"
  where "grafo_infinito G \<equiv> \<not> grafo_finito G"


definition grafo_enumerable :: "'v digrafo \<Rightarrow> bool"  where
 "grafo_enumerable G \<equiv> \<exists>g. enumeracion (g:: nat \<Rightarrow>'v)"


definition coloramiento :: "('v \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'v digrafo \<Rightarrow> bool" where
   "coloramiento c k G  \<equiv>
    (\<forall>u. u\<in>V[G]\<longrightarrow> c(u)\<le>k) \<and> (\<forall>u v.(u,v)\<in>E[G] \<longrightarrow> c(u)\<noteq>c(v))"

definition colorable ::  "'v digrafo \<Rightarrow> nat \<Rightarrow>  bool" where
    "colorable G k \<equiv> \<exists>c. coloramiento c k G"

primrec disyuncion_atomicas :: "'v \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula"  where
 "disyuncion_atomicas v  0 = Atomo (v, 0)"
| "disyuncion_atomicas v (Suc k) =
  (Atomo (v, Suc k)) \<or>. (disyuncion_atomicas v  k)"

definition \<F> :: "'v digrafo \<Rightarrow> nat \<Rightarrow> (('v \<times> nat)formula) set"  where
   "\<F> G k \<equiv> (\<Union>v\<in>V[G]. {disyuncion_atomicas v  k})"

definition \<G> :: "'v digrafo \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula set"  where
   "\<G> G k \<equiv> {\<not>.(Atomo (v, i) \<and>. Atomo(v,j))
                         | v i j. (v\<in>V[G]) \<and> (0\<le>i \<and> 0\<le>j \<and> i\<le>k \<and> j\<le>k \<and> i\<noteq>j)}"

definition \<H> :: "'v digrafo \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula set"  where
   "\<H> G k \<equiv> {\<not>.(Atomo (u, i) \<and>. Atomo(v,i))
                         |u v i . (u\<in>V[G] \<and> v\<in>V[G] \<and> (u,v)\<in>E[G]) \<and> (0\<le>i \<and> i\<le>k)} "

definition \<T> :: "'v digrafo \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula set"  where
   "\<T> G k  \<equiv> (\<F> G k) \<union> (\<G> G k) \<union> (\<H> G k)"

primrec vertices_formula :: "('v \<times> nat)formula  \<Rightarrow> 'v set" where
  "vertices_formula FF = {}"
| "vertices_formula TT = {}"
| "vertices_formula (Atomo P) =  {fst P}"
| "vertices_formula (\<not>. F) = vertices_formula F"
| "vertices_formula (F \<and>. G) = vertices_formula F \<union> vertices_formula G"
| "vertices_formula (F \<or>. G) = vertices_formula F \<union> vertices_formula G"
| "vertices_formula (F \<rightarrow>.G) = vertices_formula F \<union> vertices_formula G"

definition vertices_conjunto_formulas :: "('v \<times> nat)formula set  \<Rightarrow> 'v set" where
"vertices_conjunto_formulas S = (\<Union>F\<in> S. vertices_formula F)"

lemma finito_vertices:
  shows "finite (vertices_formula F)"
  by(induct F, auto)

lemma vertices_disyuncion:
  assumes "F = disyuncion_atomicas v  k" shows "vertices_formula F = {v}"
proof-
  have  "F = disyuncion_atomicas v  k \<Longrightarrow> vertices_formula F = {v}"
  proof(induct k arbitrary: F)
    case 0
    assume  "F = disyuncion_atomicas v 0"
    hence "F =  Atomo (v, 0 )" by auto
    thus "vertices_formula F = {v}" by auto
  next
    case(Suc k)
    have "F =(Atomo (v, Suc k )) \<or>. (disyuncion_atomicas v  k)"
      using Suc(2) by auto
    hence "vertices_formula F = vertices_formula (Atomo (v, Suc k )) \<union> vertices_formula (disyuncion_atomicas v  k)" by auto
    hence "vertices_formula F = {v} \<union> vertices_formula (disyuncion_atomicas v  k)"
      by auto
    hence "vertices_formula F = {v} \<union> {v}" using Suc(1) by auto
    thus "vertices_formula F = {v}" by auto
  qed
  thus  ?thesis using assms by auto
qed

lemma vertices_algun:
  shows "vertices_conjunto_formulas (\<F> G k) \<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_conjunto_formulas (\<F> G k)" show  "x \<in> V[G]"
  proof-
    have "x \<in> (\<Union>F\<in>(\<F> G k). vertices_formula F)" using hip
      by(unfold vertices_conjunto_formulas_def,auto)
    hence "\<exists>F\<in>(\<F> G k). x \<in> vertices_formula F" by auto
    then obtain F where "F\<in>(\<F> G k)" and x: "x \<in> vertices_formula F" by auto
    hence "\<exists> v\<in>V[G]. F\<in>{disyuncion_atomicas v  k}" by (unfold \<F>_def, auto)
    then obtain v where v: "v\<in>V[G]" and "F\<in>{disyuncion_atomicas v  k}" by auto
    hence "F = disyuncion_atomicas v  k" by auto
    hence "vertices_formula F = {v}"
      using vertices_disyuncion[OF `F = disyuncion_atomicas v  k`] by auto
    hence "x = v" using x by auto
    thus ?thesis using v by auto
  qed
qed

lemma vertices_maximoC:
  shows "vertices_conjunto_formulas(\<G> G k) \<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_conjunto_formulas (\<G> G k)" show  "x \<in> V[G]"
  proof-
    have "x \<in> (\<Union>F\<in>(\<G> G k). vertices_formula F)" using hip
      by(unfold vertices_conjunto_formulas_def,auto)
    hence "\<exists>F\<in>(\<G> G k). x \<in> vertices_formula F" by auto
    then obtain F where "F\<in>(\<G> G k)" and x: "x \<in> vertices_formula F"
      by auto
    hence "\<exists>v i j. v\<in>V[G] \<and> F =  \<not>.(Atomo (v, i) \<and>. Atomo(v,j))"
      by (unfold \<G>_def, auto)
    then obtain v i j where  "v\<in>V[G]"  and "F =  \<not>.(Atomo (v, i) \<and>. Atomo(v,j))"
      by auto
    hence v: "v\<in>V[G]"  and "F =  \<not>.(Atomo (v, i) \<and>. Atomo(v,j))" by auto
    hence v: "v\<in>V[G]"  and "vertices_formula F = {v}" by auto
    thus "x \<in> V[G]" using x by auto
  qed
qed

lemma vertices_diferentesC:
  shows "vertices_conjunto_formulas(\<H> G k)\<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_conjunto_formulas (\<H> G k)" show "x \<in> V[G]"
  proof-
    have "x \<in> (\<Union>F\<in>(\<H> G k). vertices_formula F)" using hip
      by(unfold vertices_conjunto_formulas_def,auto)
    hence "\<exists>F\<in>(\<H> G k) . x \<in> vertices_formula F" by auto
    then obtain F where "F\<in>(\<H> G k)" and x: "x \<in> vertices_formula F"
      by auto
    hence "\<exists>u v i . u\<in>V[G] \<and>  v\<in>V[G] \<and>  F =  \<not>.(Atomo (u, i) \<and>. Atomo(v,i))"
      by (unfold \<H>_def, auto)
    then obtain u v i
      where "u\<in>V[G]" and "v\<in>V[G]"  and "F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i))"
      by auto
    hence  "u\<in>V[G]" and  "v\<in>V[G]" and "F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i))"
      by auto
    hence u: "u\<in>V[G]" and v: "v\<in>V[G]" and "vertices_formula F = {u, v}"
      by auto
    hence "x=u \<or> x=v"  using x by auto
    thus "x \<in> V[G]" using u v  by auto
  qed
qed

lemma vv:
  shows "vertices_conjunto_formulas (A \<union> B) = (vertices_conjunto_formulas A) \<union> (vertices_conjunto_formulas B)"
  by(unfold  vertices_conjunto_formulas_def, auto)

lemma vv1:
  assumes "F\<in>(\<F> G k)"
  shows "(vertices_formula F) \<subseteq> (vertices_conjunto_formulas (\<F> G k))"
proof
  fix x
  assume hip: "x \<in> vertices_formula F"
  show  "x \<in> vertices_conjunto_formulas (\<F> G k)"
  proof-
    have "\<exists>F. F\<in>(\<F> G k) \<and> x \<in> vertices_formula F" using assms hip by auto
    thus  ?thesis by(unfold vertices_conjunto_formulas_def, auto)
  qed
qed

lemma vv2:
  assumes  "F\<in>(\<G> G k)"
  shows "(vertices_formula F) \<subseteq> (vertices_conjunto_formulas (\<G> G k))"
proof
  fix x
  assume hip: "x \<in> vertices_formula F"
  show  "x \<in> vertices_conjunto_formulas (\<G> G k)"
  proof-
    have "\<exists>F. F\<in>(\<G> G k) \<and> x \<in> vertices_formula F" using assms hip by auto
    thus ?thesis by(unfold vertices_conjunto_formulas_def, auto)
  qed
qed

lemma vv3:
  assumes  "F\<in>(\<H> G k)"
  shows "(vertices_formula F) \<subseteq> (vertices_conjunto_formulas (\<H> G k))"
proof
  fix x
  assume hip: "x \<in> vertices_formula F"
  show  "x \<in> vertices_conjunto_formulas (\<H> G k)"
  proof-
    have "\<exists>F. F\<in>(\<H> G k) \<and> x \<in> vertices_formula F" using assms hip by auto
    thus ?thesis by(unfold vertices_conjunto_formulas_def, auto)
  qed
qed

lemma aa:
  shows "vertices_conjunto_formulas (\<T> G k) \<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_conjunto_formulas (\<T> G k)" show "x \<in> V[G]"
  proof-
    have  "x \<in> vertices_conjunto_formulas ((\<F> G k) \<union> (\<G> G k)  \<union> (\<H> G k))"
      using hip by (unfold \<T>_def,auto)
    hence "x \<in> vertices_conjunto_formulas ((\<F> G k) \<union> (\<G> G k)) \<union>
    vertices_conjunto_formulas(\<H> G k)"
      using vv[of "(\<F> G k) \<union> (\<G> G k)"] by auto
    hence "x \<in> vertices_conjunto_formulas ((\<F> G k) \<union> (\<G> G k)) \<or>
    x \<in> vertices_conjunto_formulas(\<H> G k)"
      by auto
    thus ?thesis
    proof(rule disjE)
      assume hip: "x \<in> vertices_conjunto_formulas (\<F> G k \<union> \<G> G k)"
      hence "x \<in> (\<Union>F\<in> (\<F> G k) \<union> (\<G> G k). vertices_formula F)"
        by(unfold  vertices_conjunto_formulas_def, auto)
      then obtain F
      where F: "F\<in>(\<F> G k) \<union> (\<G> G k)" and x: "x \<in> vertices_formula F" by auto
      from F have  "(vertices_formula F) \<subseteq> (vertices_conjunto_formulas (\<F> G k))
      \<or> vertices_formula F \<subseteq> (vertices_conjunto_formulas (\<G> G k))"
        using vv1 vv2 by blast
      hence "x \<in> vertices_conjunto_formulas (\<F> G k) \<or> x \<in> vertices_conjunto_formulas (\<G> G k)"
        using x by auto
      thus "x \<in> V[G]"
        using vertices_algun[of "G" "k"] vertices_maximoC[of "G" "k"] by auto
      next
      assume "x \<in> vertices_conjunto_formulas (\<H> G k)"
      hence
      "x \<in> (\<Union>F\<in>(\<H> G k). vertices_formula F)"
        by(unfold  vertices_conjunto_formulas_def, auto)
      then obtain F where F:  "F\<in>(\<H> G k)" and x: "x \<in> vertices_formula F"
        by auto
      from F have "(vertices_formula F) \<subseteq> (vertices_conjunto_formulas (\<H> G k))"
        using vv3 by blast
      hence "x \<in> vertices_conjunto_formulas (\<H> G k)" using x by auto
      thus "x \<in> V[G]" using vertices_diferentesC[of "G" "k"]
        by auto
    qed
  qed
qed

lemma vsf:
  assumes "G \<subseteq> H"
  shows "vertices_conjunto_formulas G \<subseteq> vertices_conjunto_formulas H"
  using assms by(unfold vertices_conjunto_formulas_def, auto)

lemma vertices_subconjunto_formulas:
  assumes "S \<subseteq> (\<T> G k)"
  shows "vertices_conjunto_formulas S \<subseteq> V[G]"
proof-
  have "vertices_conjunto_formulas S \<subseteq> vertices_conjunto_formulas (\<T> G k)"
  using assms vsf by auto
  thus ?thesis using aa[of "G"] by auto
qed

definition subgrafo_aux :: "'v digrafo \<Rightarrow> 'v set \<Rightarrow>'v digrafo" where
  "subgrafo_aux G V \<equiv>  (V, E[G] \<inter> (V \<times> V))"

lemma subgrafo_inducido:
 assumes "es_grafo G" and "S \<subseteq>(\<T> G k)"
 shows "es_subgrafo_inducido (subgrafo_aux G (vertices_conjunto_formulas S)) G"
proof-
  let ?V = "vertices_conjunto_formulas S"
  let ?H = "(?V, E[G] \<inter> (?V \<times> ?V))"
  have 1: "E[?H] =  E[G] \<inter> (?V \<times> ?V)" and 2: "V[?H]= ?V"  by auto
  have "(V[?H] \<subseteq> V[G])"
  using 2 assms(2) vertices_subconjunto_formulas[of S G ]
  by auto
  moreover
  have "E[?H] = (E[G] \<inter> ((V[?H]) \<times> (V[?H])))" using 1 2 by auto
  ultimately
  have  "es_subgrafo_inducido ?H G" by(unfold es_subgrafo_inducido_def, auto)
  thus ?thesis  by(unfold subgrafo_aux_def, auto)
qed

lemma finito_subgrafo:
  assumes "es_grafo G" and "S \<subseteq> (\<T> G k)" and "finite S"
 shows "grafo_finito (subgrafo_aux G (vertices_conjunto_formulas S))"
proof-
  let ?V = "vertices_conjunto_formulas S"
  let ?H = "(?V, E[G] \<inter> (?V \<times> ?V))"
  have 1: "E[?H] =  E[G] \<inter> (?V \<times> ?V)" and 2: "V[?H]= ?V"  by auto
  have 3: "finite ?V" using `finite S` finito_vertices
    by(unfold vertices_conjunto_formulas_def, auto)
  hence  "finite (V[?H])" using 2 by auto
  moreover
  have  "finite (E[G] \<inter> (?V \<times> ?V))" using 3 by auto
  hence "finite (E[?H])" using 1 by auto
  ultimately have  "grafo_finito ?H" by(unfold grafo_finito_def, auto)
  thus ?thesis  by(unfold subgrafo_aux_def, auto)
qed

fun interpretacion_grafo :: "'v digrafo \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> (('v \<times> nat) \<Rightarrow> v_verdad)"  where
"interpretacion_grafo G f = (\<lambda>(v,i).(if v \<in> V[G] \<and> f(v) = i  then Verdad else Falso))"

lemma valor1:
  assumes "v \<in> V[G]" and "f(v)\<le> k"  and  "F = disyuncion_atomicas v  k"
  shows "valor (interpretacion_grafo G f) F = Verdad"
proof-
  let ?i = "f(v)"
  have "0 \<le> ?i" by auto
   {have  "v \<in> V[G] \<Longrightarrow> 0 \<le> ?i \<Longrightarrow> ?i\<le>k \<Longrightarrow> F = disyuncion_atomicas v  k \<Longrightarrow>
   valor (interpretacion_grafo G f) F = Verdad"
  proof(induct k arbitrary: F)
    case 0
    have "?i = 0" using "0" (2-3)  by auto
    hence "valor (interpretacion_grafo G f) (Atomo (v, 0)) =  Verdad"
      using `v \<in> V[G]`  by auto
    thus ?case using  "0" (4)  by auto
    next
    case(Suc k)
    from Suc(1) Suc(2) Suc(3) Suc(4) Suc(5) show ?case
    proof(cases)
      assume "(Suc  k) = ?i"
      hence "valor (interpretacion_grafo G f) (Atomo (v,Suc  k )) =  Verdad"
      using Suc(2) Suc(3) Suc(5) by auto
      hence
      "valor (interpretacion_grafo G f) (Atomo (v, Suc  k)
       \<or>.disyuncion_atomicas v  k) = Verdad"
      using v_disyuncion_def by auto
      thus ?case using  Suc(5) by auto
      next
      assume 1: "(Suc  k) \<noteq> ?i"
      hence "valor (interpretacion_grafo G f) (Atomo (v, Suc k)) =  Falso"
        using Suc(5) by auto
      moreover
      have "?i < (Suc  k)" using Suc(4) 1  by auto
      hence "?i \<le> k" by auto
      hence "valor (interpretacion_grafo G f) (disyuncion_atomicas v k) = Verdad"
      using  Suc(1) Suc(2) Suc(3)  Suc(5)  by auto
      thus ?case using  Suc(5)  v_disyuncion_def by auto
    qed
  qed
 }
  thus ?thesis using assms by auto
qed

lemma valor_vertice:
  assumes  "valor (interpretacion_grafo G f) (Atomo (v, i)) = Verdad"
  shows  "f(v)=i"
proof(rule ccontr)
  assume  "f v \<noteq> i" hence "valor (interpretacion_grafo G f) (Atomo (v, i)) \<noteq> Verdad" by auto
  hence "valor (interpretacion_grafo G f) (Atomo (v, i)) = Falso"
  using no_verdad[of "interpretacion_grafo G f" "Atomo (v, i)"] by auto
  thus False using assms by simp
qed

lemma valor2:
  assumes  "i\<noteq>j" and "F =\<not>.(Atomo (v, i) \<and>. Atomo (v, j))"
  shows "valor (interpretacion_grafo G f) F = Verdad"
proof(rule ccontr)
  assume "valor (interpretacion_grafo G f) F \<noteq> Verdad"
  hence  "valor (interpretacion_grafo G f) (\<not>.(Atomo (v, i) \<and>. Atomo (v, j))) \<noteq> Verdad"
    using assms(2) by auto
  hence "valor (interpretacion_grafo G f) (\<not>.(Atomo (v, i) \<and>. Atomo (v, j))) = Falso" using
  no_verdad[of "interpretacion_grafo G f" "\<not>.(Atomo (v, i) \<and>. Atomo (v, j))" ]
    by auto
  hence  "valor (interpretacion_grafo G f) ((Atomo (v, i) \<and>. Atomo (v, j))) = Verdad"
  using  ValoresNegacion1[of "interpretacion_grafo G f" "(Atomo (v, i) \<and>. Atomo (v, j))"] by auto
  hence "valor (interpretacion_grafo G f) (Atomo (v, i)) = Verdad" and
  "valor (interpretacion_grafo G f) (Atomo (v, j)) = Verdad"
  using ValoresConjuncion[of "interpretacion_grafo G f" "Atomo (v, i)" "Atomo (v, j)"] by auto
  hence "f(v)=i" and "f(v)=j" using valor_vertice by auto
  hence "i=j" by auto
  thus False using assms(1) by auto
qed

lemma valor3:
  assumes "f(u)\<noteq>f(v)" and  "F =\<not>.(Atomo (u, i) \<and>. Atomo (v, i))"
  shows "valor (interpretacion_grafo G f) F = Verdad"
proof(rule ccontr)
  assume "valor (interpretacion_grafo G f) F \<noteq> Verdad"
  hence(*and "finite S"*)
  "valor (interpretacion_grafo G f) (\<not>.(Atomo (u, i) \<and>. Atomo (v, i))) \<noteq> Verdad"
    using assms(2) by auto
  hence "valor (interpretacion_grafo G f) (\<not>.(Atomo (u, i) \<and>. Atomo (v, i))) = Falso"
    using
  no_verdad[of "interpretacion_grafo G f" "\<not>.(Atomo (u, i) \<and>. Atomo (v, i))"]
    by auto
  hence  "valor (interpretacion_grafo G f) ((Atomo (u, i) \<and>. Atomo (v, i))) = Verdad"
    using  ValoresNegacion1[of "interpretacion_grafo G f" "(Atomo (u, i) \<and>. Atomo (v, i))"]
    by auto
  hence "valor (interpretacion_grafo G f) (Atomo (u, i)) = Verdad" and
  "valor (interpretacion_grafo G f) (Atomo (v, i)) = Verdad"
    using ValoresConjuncion[of "interpretacion_grafo G f" "Atomo (u, i)" "Atomo (v, i)"]
    by auto
  hence "f(u)=i" and "f(v)=i" using valor_vertice by auto
  hence "f(u)=f(v)" by auto
  thus False using assms(1) by auto
qed

theorem coloramiento_satisfactible:
  assumes "es_grafo G" and "S \<subseteq> (\<T> G k)" and
  "coloramiento f k (subgrafo_aux G (vertices_conjunto_formulas S))"
  shows "satisfacible S"
proof-
  let ?V = "vertices_conjunto_formulas S"
  let ?H = "subgrafo_aux G ?V"
  have "(interpretacion_grafo ?H f) modelo S"
  proof(unfold modelo_def)
    show "\<forall> F \<in> S. valor (interpretacion_grafo ?H f) F  = Verdad"
    proof
      fix F assume "F \<in> S"
      show  "valor (interpretacion_grafo ?H f) F  = Verdad"
      proof-
        have 1:  "vertices_formula F \<subseteq>?V"
        proof
          fix v
          assume "v \<in> (vertices_formula F)" thus "v \<in> ?V"
          using `F \<in> S` by(unfold vertices_conjunto_formulas_def,auto)
        qed
        have "F \<in> (\<F> G k) \<union> (\<G> G k)  \<union> (\<H> G k)"
        using  `F \<in> S` assms(2)  by(unfold \<T>_def,auto)
        hence  "F \<in> (\<F> G k) \<or> F \<in> (\<G> G k) \<or> F \<in> (\<H> G k)" by auto
        thus ?thesis
        proof(rule disjE)
          assume "F \<in> (\<F> G k)"
          hence "\<exists>v\<in>V[G]. F = disyuncion_atomicas v  k"  by(unfold \<F>_def,auto)
          then obtain v
          where v: "v\<in>V[G]" and F: "F = disyuncion_atomicas v k"
            by auto
          have "v\<in>?V" using F vertices_disyuncion[of "F"] 1 by auto
          hence "v\<in> V[?H]" by(unfold subgrafo_aux_def, auto)
          hence "f(v)\<le> k" using coloramiento_def[of "f" "k" "?H"] assms(3) by auto
          thus ?thesis using F  valor1[OF `v\<in>V[?H]`] by auto
          next
          assume "F \<in> (\<G> G k) \<or> F \<in> (\<H> G k)"
          thus ?thesis
          proof(rule disjE)
            assume "F \<in> (\<G> G k)"
            hence "\<exists>v.\<exists>i.\<exists>j. F = \<not>.(Atomo (v, i) \<and>. Atomo(v,j)) \<and> ( i\<noteq>j)"
            by(unfold \<G>_def, auto)
            then obtain v i j
            where "F = \<not>.(Atomo (v, i) \<and>. Atomo(v,j))" and "(i\<noteq>j)"
            by auto
            thus "valor (interpretacion_grafo ?H f) F = Verdad"
            using valor2[OF `i\<noteq>j` `F = \<not>.(Atomo (v, i) \<and>. Atomo(v,j))`]
            by auto
            next
            assume " F \<in> (\<H> G k)"
            hence  "\<exists>u.\<exists>v.\<exists>i.(F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i)) \<and>  (u,v)\<in>E[G])"
            by(unfold \<H>_def, auto)
            then obtain u v i
            where F:  "F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i))" and uv: "(u,v)\<in>E[G]"
            by auto
            have "vertices_formula F = {u,v}" using F by auto
            hence "{u,v} \<subseteq> ?V" using 1 by auto
            hence "(u,v)\<in>E[?H]" using uv  by(unfold subgrafo_aux_def, auto)
            hence  "f(u) \<noteq>f(v)" using  coloramiento_def[of "f" "k" "?H"] assms(3)
              by auto
            show ?thesis
              using valor3[OF `f(u) \<noteq>f(v)` `F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i))`]
              by auto
          qed
        qed
      qed
    qed
  qed
  thus "satisfacible S" by(unfold satisfacible_def, auto)
qed

(* El siguiente teorema no se necesita. *)
theorem coloramiento_satisfactible1:
  assumes "coloramiento f k G"
  shows "satisfacible (\<T> G k)"
proof-
  let ?S = "(\<T> G k)"
  have "\<forall> F \<in> ?S. valor (interpretacion_grafo G f) F = Verdad"
  proof
    fix F assume "F \<in> ?S"
    show "valor (interpretacion_grafo G f) F = Verdad"
    proof-
      have "F \<in> (\<F> G k) \<union> (\<G> G k) \<union> (\<H> G k)"
      using `F \<in> ?S` by(unfold \<T>_def,auto)
      hence  "F \<in> (\<F> G k) \<or> F \<in> (\<G> G k) \<or> F \<in> (\<H> G k)" by auto
      thus ?thesis
    proof(rule disjE)
      assume "F \<in> \<F> G k"
      hence "\<exists>v\<in>V[G]. F = disyuncion_atomicas v  k"  by(unfold \<F>_def,auto)
      then obtain v
      where v: "v\<in>V[G]" and F: "F = disyuncion_atomicas v  k" by auto
      have "f(v)\<le> k"
        using v and  coloramiento_def[of "f" "k" "G"] assms by auto
      thus ?thesis using F valor1[OF `v\<in>V[G]`] by blast
      next
      assume "F \<in> (\<G> G k) \<or> F \<in> (\<H> G k)"
      thus ?thesis
      proof(rule disjE)
        assume "F \<in> (\<G> G k)"
        hence  "\<exists>v.\<exists>i.\<exists>j. F = \<not>.(Atomo (v, i) \<and>. Atomo(v,j)) \<and> ( i\<noteq>j)"
        by(unfold \<G>_def, auto)
        then obtain v i j
        where "F = \<not>.(Atomo (v, i) \<and>. Atomo(v,j))" and "(i\<noteq>j)" by auto
        thus "valor (interpretacion_grafo G f) F  = Verdad"
        using valor2[OF `i\<noteq>j`  `F = \<not>.(Atomo (v, i) \<and>. Atomo(v,j))` ] by auto
        next
        assume " F \<in> (\<H> G k)"
        hence  "\<exists>u.\<exists>v.\<exists>i.(F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i)) \<and>  (u,v)\<in>E[G])"
        by(unfold \<H>_def, auto)
        then obtain u v i
        where F:  "F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i))" and uv: "(u,v)\<in>E[G]"
        by auto
      have "f(u) \<noteq>f(v)"
        using uv and  coloramiento_def[of "f" "k" "G"] assms by auto
        show ?thesis
          using valor3[OF `f(u) \<noteq>f(v)` `F = \<not>.(Atomo (u, i) \<and>. Atomo(v,i))`]
        by auto
        qed
      qed
    qed
  qed
  hence "(interpretacion_grafo G f) modelo ?S" by(unfold modelo_def)
  thus "satisfacible ?S" by( unfold satisfacible_def,auto)
qed

lemma diag_nat:
  shows "\<forall>y z.\<exists>x. (y,z) = diag x"
  using enumeracion_natxnat by(unfold enumeracion_def,auto)

lemma EnumFormulasVertices:
  assumes "\<exists>g. enumeracion (g:: nat \<Rightarrow>'v)"
  shows "\<exists>f. enumeracion (f:: nat \<Rightarrow>('v \<times> nat)formula)"
proof-
  from assms obtain g where e: "enumeracion (g:: nat \<Rightarrow>'v)" by auto
  have  "enumeracion ((\<lambda>m.(g(fst(diag m)),snd(diag m))):: nat \<Rightarrow>('v \<times> nat))"
  proof(unfold enumeracion_def)
    show  "\<forall>y::('v \<times> nat). \<exists>m. y = (g (fst (diag m)), snd (diag m))"
    proof
      fix y::"('v \<times> nat)"
      show "\<exists>m. y = (g (fst (diag m)), snd (diag m))"
      proof-
        have  "y = ((fst y), (snd y))" by auto
        from e have  "\<forall>w::'v. \<exists>n. w = (g n)" by(unfold enumeracion_def, auto)
        hence  "\<exists>n. (fst y) = (g n)" by auto
        then obtain n where n: "(fst y) = (g n)" by auto
        have "\<exists>m. (n, (snd y)) = diag m" using diag_nat by auto
        hence "\<exists>m. (n, (snd y)) = (fst (diag m), snd (diag m))" by simp
        hence "\<exists>m.((fst y), (snd y)) = (g(fst (diag m)), snd (diag m))"
          using n by blast
        thus "\<exists>m. y = (g (fst (diag m)), snd (diag m))" by auto
      qed
    qed
  qed
  thus "\<exists>f. enumeracion (f:: nat \<Rightarrow>('v \<times> nat)formula)"
    using EnumeracionFormulasP1 by auto
qed

fun coloramiento_grafo ::  "(('v \<times> nat) \<Rightarrow> v_verdad) \<Rightarrow> nat  \<Rightarrow> ('v \<Rightarrow> nat)"
  where
"coloramiento_grafo I k = (\<lambda>v.(THE i. (valor I (Atomo (v,i)) = Verdad) \<and> 0\<le>i \<and> i\<le>k))"

lemma unicidad:
  assumes "(valor I (Atomo (v, i)) = Verdad \<and> 0\<le>i \<and> i \<le> k)"
  and "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (valor I (\<not>.(Atomo (v, i) \<and>. Atomo(v,j))) = Verdad)"
  shows "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  valor I (Atomo (v, j)) = Falso"
proof(rule allI, rule impI)
  fix j
  assume hip: "0\<le>j \<and> j\<le>k \<and> i\<noteq>j"
  show "valor I (Atomo (v, j)) = Falso"
  proof(rule ccontr)
    assume "valor I (Atomo (v, j)) \<noteq> Falso"
    hence "valor I (Atomo (v, j)) = Verdad" using CasosValor by blast
    hence 1: "valor I (Atomo (v, i) \<and>. Atomo(v,j))  = Verdad"
      using assms(1) v_conjuncion_def by auto
    have "valor I (\<not>.(Atomo (v, i) \<and>. Atomo(v,j))) = Verdad"
      using hip assms(2)  by auto
    hence "valor I (Atomo (v, i) \<and>. Atomo(v,j)) = Falso"
      using ValoresNegacion2  by blast
    thus False using 1  by auto
  qed
qed

lemma existencia:
  assumes "(valor I (Atomo (v, i)) = Verdad \<and> 0\<le>i \<and> i \<le> k)"
  and  "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  valor I (Atomo (v, j)) = Falso"
shows  "(\<forall>x. (valor I (Atomo (v, x)) = Verdad \<and> 0\<le>x \<and> x \<le> k) \<longrightarrow> x = i)"
proof(rule allI)
  fix x
  show "valor I (Atomo (v, x)) = Verdad \<and> 0 \<le> x \<and> x \<le> k \<longrightarrow> x = i"
  proof(rule impI)
    assume hip: "valor I (Atomo (v, x)) = Verdad \<and> 0\<le>x \<and> x \<le> k" show "x = i"
    proof(rule ccontr)
      assume 1:  "x \<noteq> i"
      have  "0\<le>x \<and> x \<le> k" using hip by auto
      hence "valor I (Atomo (v, x)) = Falso" using 1 assms(2) by auto
      thus False using hip by auto
    qed
  qed
qed

lemma exist_unicidad1:
  assumes  "(valor I (Atomo (v, i)) = Verdad \<and> 0\<le>i \<and> i \<le> k)"
  and "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (valor I (\<not>.(Atomo (v, i) \<and>. Atomo(v,j))) = Verdad)"
shows "(\<forall>x. (valor I (Atomo (v, x)) = Verdad \<and> 0\<le>x \<and> x \<le> k) \<longrightarrow> x = i)"
using assms  unicidad[of "I" "v" "i" "k" ] existencia[of "I" "v" "i" "k"]  by blast

lemma exist_unicidad2:
  assumes "(valor I (Atomo (v, i)) = Verdad \<and> 0\<le>i \<and> i \<le> k )" and
  "(\<And>x. (valor I (Atomo (v, x)) = Verdad \<and> 0\<le>x \<and> x \<le> k) \<Longrightarrow> x = i)"
shows "(THE a. (valor I (Atomo (v,a)) = Verdad \<and> 0\<le>a \<and> a \<le> k )) = i"
  using assms by (rule the_equality)

lemma exist_unicidad:
  assumes "(valor I (Atomo (v, i)) = Verdad \<and> 0\<le>i \<and> i\<le>k )" and
  "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (valor I (\<not>.(Atomo (v, i) \<and>. Atomo(v,j))) = Verdad)"
shows "(THE a. (valor I (Atomo (v,a)) = Verdad \<and> 0\<le>a \<and> a \<le> k )) = i"
 using assms  exist_unicidad1[of "I" "v" "i" "k" ] exist_unicidad2[of "I" "v" "i" "k"] by blast

lemma elem_max_un_color:
  assumes  "v \<in> V[G]"
  shows "\<forall>i j.(0\<le>i \<and> 0\<le>j \<and> i\<le>k \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  (\<not>.(Atomo (v, i) \<and>. Atomo(v,j))\<in> (\<G> G k))"
proof(rule allI )+
  fix i j
  show "0 \<le> i \<and> 0 \<le> j \<and> i \<le> k \<and> j \<le> k \<and> i \<noteq> j \<longrightarrow> \<not>.(Atomo (v, i) \<and>. Atomo (v, j)) \<in> (\<G> G k)"
  proof(rule impI)
    assume "0 \<le> i \<and> 0 \<le> j \<and> i \<le> k \<and> j \<le> k \<and> i \<noteq> j"
    thus "\<not>.(Atomo (v, i) \<and>. Atomo (v, j)) \<in> (\<G> G k)"
      using `v \<in> V[G]` by(unfold  \<G>_def, auto)
  qed
qed
(* El siguiente lema no se necesita. *)
lemma elem_dif_colores:
  assumes  "u \<in> V[G]" and  "v\<in>V[G]" and "(u,v)\<in>E[G]"
  shows  "\<forall>i.(0\<le>i \<and> i\<le>k) \<longrightarrow>  (\<not>.(Atomo (u, i) \<and>. Atomo(v,i))\<in> (\<H> G k))"
proof(rule allI)
  fix i
  show "0\<le>i \<and> i\<le>k \<longrightarrow>  (\<not>.(Atomo (u, i) \<and>. Atomo(v,i))\<in> (\<H> G k))"
  proof(rule impI)
    assume "0\<le>i \<and> i\<le>k"
    thus  "\<not>.(Atomo (u, i) \<and>. Atomo(v,i))\<in> (\<H> G k)"
      using assms  by(unfold  \<H>_def, auto)
  qed
qed

lemma valor_atomo:
  assumes "(valor I (disyuncion_atomicas u  k)) = Verdad"
  shows "\<exists>i.(valor I (Atomo (u,i)) = Verdad) \<and> 0\<le>i \<and> i\<le>k"
proof-
  have "(valor I (disyuncion_atomicas u  k)) = Verdad \<Longrightarrow>
  \<exists>i.(valor I (Atomo (u,i)) = Verdad) \<and> 0\<le>i \<and> i\<le>k"
  proof(induct k)
    case(0)
    assume "(valor I (disyuncion_atomicas u 0)) = Verdad"
    thus "\<exists>i. valor I (Atomo (u, i)) = Verdad \<and> 0\<le>i \<and>  i \<le> 0" by auto
    next
    case(Suc k)
    from Suc(1) Suc(2) show ?case
    proof-
      have "valor I (Atomo (u, (Suc k)) \<or>. (disyuncion_atomicas u k)) = Verdad"
        using Suc(2) by auto
      hence "valor I (Atomo (u, (Suc k))) = Verdad \<or>
      (valor I (disyuncion_atomicas u k)) = Verdad"
        using  ValoresDisyuncion[of I "(Atomo (u, (Suc k)))"] by auto
      thus ?case
      proof(rule disjE)
        assume "valor I (Atomo (u, (Suc k))) = Verdad"
        thus ?case  by(rule_tac  x= "Suc k" in exI, auto)
        next
        assume "valor I (disyuncion_atomicas u k) = Verdad"
        thus ?case using Suc(1) by auto
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma funcion_coloramiento:
  assumes "u \<in> V[G]" and  "I modelo (\<F> G k)" and "I modelo (\<G> G k)"
  shows "\<exists>!i. (valor I (Atomo (u,i)) = Verdad \<and> 0\<le>i \<and> i\<le>k) \<and> coloramiento_grafo I k u = i"
proof-
  from  `u \<in> V[G]`
  have "disyuncion_atomicas u  k \<in> \<F> G k" by(induct, unfold  \<F>_def, auto)
  hence "(valor I (disyuncion_atomicas u  k)) = Verdad"
    using assms(2) modelo_def[of I "\<F> G k"] by auto
  hence "\<exists>i.(valor I (Atomo (u,i)) = Verdad \<and> 0\<le>i \<and> i\<le>k)"
    using valor_atomo by auto
  then obtain i where i: "(valor I (Atomo (u,i)) = Verdad) \<and> 0\<le>i \<and> i\<le>k"
    by auto
  moreover
  have "\<forall>i j.(0\<le>i \<and> 0\<le>j \<and> i\<le>k \<and> j\<le>k \<and> i\<noteq>j)\<longrightarrow>
  (\<not>.(Atomo (u, i) \<and>.Atomo(u,j))\<in> (\<G> G k))"
    using `u \<in> V[G]` elem_max_un_color[of "u"] by auto
  hence "\<forall>j.(0\<le>j  \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  (\<not>.(Atomo (u, i) \<and>. Atomo(u,j))\<in> \<G> G k)"
  using i by auto
  hence
  "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (valor I (\<not>.(Atomo (u, i) \<and>. Atomo(u,j))) = Verdad)"
  using assms(3)  modelo_def[of I "\<G> G k"] by blast
  hence "(THE a. (valor I (Atomo (u,a)) = Verdad \<and> 0\<le>a \<and> a \<le> k ))= i"
    using i exist_unicidad[of "I" "u"] by blast
  hence "coloramiento_grafo I k u = i" by auto
  hence
  "(valor I (Atomo (u,i)) = Verdad \<and> 0\<le>i \<and>  i\<le>k) \<and>
   coloramiento_grafo I k u = i"
    using i by auto
  thus ?thesis  by auto
qed

lemma \<H>1:
  assumes "(valor I (Atomo (u, a)) = Verdad \<and> 0\<le>a \<and> a\<le>k )" and
          "(valor I (Atomo (v, b)) = Verdad \<and> 0\<le>b \<and> b\<le>k)"
  and "\<forall>i.(0\<le>i \<and> i\<le>k) \<longrightarrow> (valor I (\<not>.(Atomo (u, i) \<and>. Atomo(v,i))) = Verdad)"
  shows "a\<noteq>b"
proof(rule ccontr)
  assume  "\<not> a \<noteq> b"
  hence "a=b" by auto
  hence "valor I (Atomo (u, a)) = Verdad" and  "valor I (Atomo (v, a)) = Verdad"
    using assms by auto
  hence "valor I (Atomo (u, a) \<and>. Atomo(v,a)) = Verdad" using v_conjuncion_def by auto
  hence "valor I (\<not>.(Atomo (u, a) \<and>. Atomo(v,a))) = Falso" using v_negacion_def by auto
  moreover
  have "0\<le>a \<and> a\<le>k" using assms(1) by auto
  hence "valor I (\<not>.(Atomo (u, a) \<and>. Atomo(v,a))) = Verdad" using assms(3) by auto
  finally show False by auto
qed

lemma modelo_colores:
  assumes  "M modelo (\<T> G k)"
  shows  "M modelo (\<F> G k)" and  "M modelo (\<G> G k)" and  "M modelo (\<H> G k)"
proof(unfold modelo_def)
  show "\<forall>F\<in>\<F> G k. valor M F = Verdad"
  proof
    fix F
    assume "F\<in> (\<F> G k)" hence "F\<in>(\<T> G k)" by(unfold \<T>_def, auto)
    thus "valor M F = Verdad" using assms by(unfold modelo_def, auto)
  qed
next
  show "\<forall>F\<in>(\<G> G k). valor M F = Verdad"
  proof
    fix F
    assume "F\<in>(\<G> G k)" hence "F\<in>(\<T> G k)" by(unfold \<T>_def, auto)
    thus "valor M F = Verdad" using assms by(unfold modelo_def, auto)
  qed
next
  show "\<forall>F\<in>(\<H> G k). valor M F = Verdad"
  proof
    fix F
    assume "F\<in>(\<H> G k)" hence "F\<in>(\<T> G k)" by(unfold \<T>_def, auto)
    thus "valor M F = Verdad" using assms by(unfold modelo_def, auto)
  qed
qed

lemma colores_distintos:
  assumes "es_grafo G" and "(u,v) \<in> E[G]" and I: "I modelo (\<T> G k)"
  shows "coloramiento_grafo I k u \<noteq> coloramiento_grafo I k v"
proof-
  have "u \<noteq> v" and "u \<in> V[G]" and "v \<in> V[G]"  using  `(u,v) \<in> E[G]` `es_grafo G`
    by(unfold es_grafo_def, auto)
  have 1: "I modelo \<F> G k" and 2:  "I modelo \<G> G k"
    using I modelo_colores[of I G k] by auto
  have "\<exists>!i. (valor I (Atomo (u,i)) = Verdad \<and> 0\<le>i \<and> i\<le>k) \<and> coloramiento_grafo I k u = i"
  using `u \<in> V[G]` 1 2 funcion_coloramiento[of u G I k]  by auto
  then obtain i where i1: "(valor I (Atomo (u,i)) = Verdad \<and> 0\<le>i \<and> i\<le>k)" and i2: "coloramiento_grafo I k u = i"
    by auto
  have  "\<exists>!j. (valor I (Atomo (v,j)) = Verdad \<and> 0\<le>j \<and>  j\<le>k) \<and> coloramiento_grafo I k v = j"
  using `v \<in> V[G]` 1 2 funcion_coloramiento[of v G I k]  by auto
  then obtain j where j1: "(valor I (Atomo (v,j)) = Verdad \<and> 0\<le>j \<and> j\<le>k)" and
   j2: "coloramiento_grafo I k v = j" by auto
  have  "\<forall>i.(0\<le>i \<and> i\<le>k) \<longrightarrow>  (\<not>.(Atomo (u, i) \<and>. Atomo(v,i))\<in> \<H> G k)"
  using `u \<in> V[G]` `v \<in> V[G]`  `(u,v) \<in> E[G]`  by(unfold  \<H>_def, auto)
  hence "\<forall>i. (0\<le>i \<and> i\<le>k) \<longrightarrow> \<not>.(Atomo (u, i) \<and>. Atomo(v,i)) \<in> \<T> G k"
  by(unfold  \<T>_def, auto)
  hence  "\<forall>i. (0\<le>i \<and> i\<le>k) \<longrightarrow> (valor I  (\<not>.(Atomo (u, i) \<and>. Atomo(v,i))) = Verdad)"
  using assms(2) I modelo_def[of I "\<T> G k"] by blast
  hence "i \<noteq> j" using i1 j1 \<H>1[of "I" "u" "i"  "k" "v" "j"] by blast
  thus ?thesis using i2 j2 by auto
qed

theorem satisfactible_coloramiento:
  assumes "es_grafo G" and  "satisfacible (\<T> G k)"
  shows  "colorable G k"
proof(unfold colorable_def)
  show "\<exists>f. coloramiento f k G"
  proof-
    from assms(2) have "\<exists>I. I modelo (\<T> G k)"  by(unfold satisfacible_def)
    then obtain I where I: "I modelo (\<T> G k)" by auto
    hence 1: "I modelo \<F> G k" and 2:  "I modelo \<G> G k"
    using I modelo_colores[of I G k] by auto
    hence  "coloramiento (coloramiento_grafo I k) k G"
    proof(unfold coloramiento_def)
      show
      "(\<forall>u. u \<in> V[G] \<longrightarrow> (coloramiento_grafo I  k u) \<le> k) \<and> (\<forall>u v. (u, v) \<in> E[G]
      \<longrightarrow> coloramiento_grafo I k u \<noteq> coloramiento_grafo I k v)"
      proof(rule conjI)
        show "\<forall>u. u \<in> V[G] \<longrightarrow> coloramiento_grafo I k u \<le> k"
        proof(rule allI, rule impI)
          fix u
          assume  "u \<in> V[G]"
          thus "coloramiento_grafo I k u \<le> k"
            using 1 2 funcion_coloramiento[of u G I k ] by auto
        qed
        next
          show
          "\<forall>u v. (u, v) \<in> E[G] \<longrightarrow>
          coloramiento_grafo I k u \<noteq> coloramiento_grafo I k v"
          proof(rule allI,rule allI,rule impI)
          fix u v
          assume "(u,v) \<in> E[G]"
          thus "coloramiento_grafo I k u \<noteq> coloramiento_grafo I k v"
          using  colores_distintos[OF `es_grafo G` `(u,v) \<in> E[G]`  I]  by blast
        qed
      qed
    qed
    thus "\<exists>f. coloramiento f k G" by auto
  qed
qed

theorem coloracion:
  assumes "es_grafo (G::('vertices set) \<times> (('vertices \<times> 'vertices) set))"
  and "\<exists>g. enumeracion (g:: nat \<Rightarrow>'vertices)"
  and "\<forall>H. (es_subgrafo_inducido H G \<and> grafo_finito H \<longrightarrow> colorable H k)"
  shows "colorable G k"
proof-
  have "\<forall> S. S \<subseteq> (\<T> G k) \<and> (finite S) \<longrightarrow> satisfacible S"
  proof(rule allI, rule impI)
    fix S assume "S \<subseteq> (\<T> G k) \<and> (finite S)"
    hence hip1:  "S \<subseteq> (\<T> G k)" and  hip2: "finite S" by auto
    show "satisfacible S"
    proof -
      let ?V = "vertices_conjunto_formulas S"
      let ?H = "(?V, E[G] \<inter> (?V \<times> ?V))"
      have "es_subgrafo_inducido ?H G"
        using assms(1) hip1 subgrafo_inducido[of G S k]
        by(unfold subgrafo_aux_def, auto)
      moreover
      have "grafo_finito ?H"
        using assms(1) hip1 hip2 finito_subgrafo[of G S k]
        by(unfold subgrafo_aux_def, auto)
      ultimately
      have "colorable ?H k" using assms(3) by auto
      hence  "\<exists>f. coloramiento f k ?H" by(unfold colorable_def, auto)
      then obtain f where "coloramiento f k ?H" by auto
      thus "satisfacible S" using coloramiento_satisfactible[OF assms(1) hip1]
        by(unfold subgrafo_aux_def, auto)
    qed
  qed
  hence "satisfacible (\<T> G k)" using
  TeoremaCompacidad1[OF EnumFormulasVertices[OF
  `\<exists>g. enumeracion (g:: nat \<Rightarrow>'v)`], of "(\<T> G k)"]
  by auto
  thus ?thesis using assms(1) satisfactible_coloramiento by blast
qed

end
