(*<*)
theory TeoriaKonig
 imports Main TeoriaCompacidad2
begin
(*>*)
section \<open> Anexo 3. Teoría König \<close>

text\<open>
Se formaliza en Isabelle/HOL, utilizando el Teorema de Compacidad para la Lógica Proposicional, el Lema de König para árboles enumerables:
\par
Todo árbol infinito enumerable de ramificación finita tiene una rama infinita.
\<close>

type_synonym 'a rel = "('a \<times> 'a) set"

definition irrefl_en ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
 where "irrefl_en A r \<equiv>  (\<forall>x\<in>A. (x, x) \<notin> r)"

definition trans_en :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "trans_en A r \<equiv>
 (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"

definition total_en :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "total_en A r \<equiv> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"

definition minimo ::  "'a set \<Rightarrow> 'a \<Rightarrow>'a rel \<Rightarrow> bool"
  where "minimo A a r \<equiv>  (a\<in>A \<and> (\<forall>x\<in>A. x \<noteq> a  \<longrightarrow> (a,x) \<in> r))"

definition predecesores_de :: "'a set \<Rightarrow>'a \<Rightarrow>'a rel  \<Rightarrow> 'a set"
  where "predecesores_de A a r \<equiv> {x\<in>A.(x, a) \<in> r}"

definition altura ::  "'a set \<Rightarrow>'a \<Rightarrow> 'a rel \<Rightarrow> nat"
  where "altura A a r   \<equiv>  card (predecesores_de A a r)"

definition nivel ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow>'a set"
  where "nivel A r n \<equiv> {x\<in>A. altura A x r = n}"

definition sucesores_inmed_de ::  "'a set \<Rightarrow> 'a \<Rightarrow> 'a rel \<Rightarrow> 'a set"
  where "sucesores_inmed_de A a r \<equiv>
 {x\<in>A. (a,x)\<in> r \<and> altura A x r = (altura A a r)+1}"

definition orden_parcial_estricto_en ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where  "orden_parcial_estricto_en A r \<equiv> irrefl_en A r \<and> trans_en A r"

definition orden_lineal_en :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "orden_lineal_en A r \<equiv> orden_parcial_estricto_en A r \<and> total_en A r"

lemma minimo_elemento:
  assumes  "orden_parcial_estricto_en A r" and "minimo A a r" and "r={}"
  shows "A={a}"
proof(rule ccontr)
  assume hip: "A \<noteq> {a}" show False
  proof(cases)
    assume  hip1: "A={}"
    have "a\<in>A" using `minimo A a r` by(unfold minimo_def, auto)
    thus False using hip1 by auto
  next
    assume  "A \<noteq> {}"
    hence "\<exists>x. x\<noteq>a \<and> x\<in>A" using hip by auto
    then obtain x where  "x\<noteq>a \<and> x\<in>A" by auto
    hence "(a,x)\<in>r"  using `minimo A a r` by(unfold minimo_def, auto)
    hence "r \<noteq> {}" by auto
    thus False using `r={}` by auto
  qed
qed

lemma unico_minimo:
  assumes  "orden_parcial_estricto_en A r" and  "minimo A a r" and "minimo A b r"
  shows "a=b"
proof(rule ccontr)
  assume hip: "a \<noteq> b"
  have "a\<in>A"and "b\<in>A" using assms(2-3) by(unfold minimo_def, auto)
  show False
  proof(cases)
    assume "r = {}"
    hence  "A={a} \<and> A={b}"  using assms(1-3) minimo_elemento[of A r] by auto
    thus False using hip by auto
  next
    assume "r\<noteq>{}"
    hence 1: "(a,b)\<in>r \<and> (b,a)\<in>r" using hip assms(2-3)
      by(unfold minimo_def, auto)
    have  irr: "irrefl_en A r" and tran: "trans_en A r"
    using assms(1) by(unfold orden_parcial_estricto_en_def, auto)
    have  "(a,a)\<in>r" using  `a\<in>A`  `b\<in>A` 1 tran by(unfold trans_en_def, blast)
    thus False using  `a\<in>A`  irr  by(unfold irrefl_en_def, blast)
  qed
qed

lemma predecesores_minimo1:
  assumes  "minimo A a r" and "orden_parcial_estricto_en A r"
  shows  "predecesores_de A a r = {}"
proof(rule ccontr)
  have  irr:  "irrefl_en A r" and tran: "trans_en A r" using assms(2)
  by(unfold orden_parcial_estricto_en_def, auto)
  assume 1: "predecesores_de A a r \<noteq> {}" show False
  proof-
    have "\<exists>x\<in>A. (x,a)\<in> r" using 1  by(unfold predecesores_de_def, auto)
    then obtain x where "x\<in>A" and "(x,a)\<in> r" by auto
    hence "x\<noteq>a" using irr by (unfold irrefl_en_def, auto)
    hence "(a,x)\<in>r" using  `x\<in>A` `minimo A a r` by(unfold minimo_def, auto)
    have  "a\<in>A" using  `minimo A a r` by(unfold minimo_def, auto)
    hence "(a,a)\<in>r" using `(a,x)\<in>r`  `(x,a)\<in> r`  `x\<in>A`  tran
      by(unfold trans_en_def, blast)
    thus False using `(a,a)\<in>r` `a\<in>A` irr  irrefl_en_def
      by (unfold irrefl_en_def, auto)
  qed
qed

lemma  predecesores_minimo2:
  assumes  "orden_parcial_estricto_en A r" and  "minimo A a r"
  shows "\<forall>x\<in>A.(predecesores_de A x r = {}) \<longleftrightarrow> (x=a)"
proof
  fix x
  assume  "x \<in> A"
  show "(predecesores_de A x r = {}) \<longleftrightarrow> (x = a)"
  proof-
    have 1: "a \<in> A" using  `minimo A a r`  by(unfold minimo_def, auto)
    have 2: "(predecesores_de A x r = {})\<longrightarrow> (x=a)"
    proof(rule impI)
      assume h: "predecesores_de A x r = {}"  show "x=a"
      proof(rule ccontr)
      assume  "x \<noteq> a"
      hence  "(a,x)\<in> r" using  `x \<in> A` `minimo A a r`
        by(unfold minimo_def, auto)
      hence  "a \<in> predecesores_de A x r"
        using 1 by(unfold  predecesores_de_def,auto)
      thus False using h by auto
    qed
  qed
  have 3: "x=a \<longrightarrow> (predecesores_de A x r = {})"
  proof(rule impI)
    assume "x=a"
    thus "predecesores_de A x r = {}"
      using assms predecesores_minimo1[of A a]  by auto
  qed
  show ?thesis using 2 3 by auto
   qed
qed

lemma altura_minimo:
  assumes  "orden_parcial_estricto_en A r" and  "minimo A a r"
  shows "altura  A a r = 0"
proof-
  have  "a\<in>A" using  `minimo A a r` by(unfold minimo_def, auto)
  hence "predecesores_de A a r = {}"
    using assms predecesores_minimo2[of A r]  by auto
  thus "altura  A a r = 0" by(unfold altura_def, auto)
qed

lemma nivel_cero:
  assumes  "orden_parcial_estricto_en A r"
  and "minimo A a r"  and  "\<forall>x\<in>A. finite (predecesores_de A x r)"
  shows "(nivel A r 0) = {a}"
proof-
  have "\<forall>x\<in>A.(card (predecesores_de A x r) = 0) \<longleftrightarrow> (x=a)"
  using  assms predecesores_minimo2[of A r a] card_eq_0_iff by auto
  hence 1:  "\<forall>x\<in>A.(altura A x r = 0) \<longleftrightarrow> (x=a)"
    by(unfold altura_def, auto)
  have "a\<in>A" using  `minimo A a r` by(unfold minimo_def, auto)
  thus ?thesis using assms 1  nivel_def[of A r 0] by auto
qed

lemma minimo_predecesor:
  assumes  "minimo A a r"
  shows  "\<forall>x\<in>A. x\<noteq>a \<longrightarrow> a\<in>predecesores_de A x r"
proof
  fix x
  assume "x\<in>A"
  show "x \<noteq> a \<longrightarrow> a \<in> predecesores_de A x r"
  proof(rule impI)
    assume  "x \<noteq> a"
    show "a \<in> predecesores_de A x r"
    proof-
      have "(a,x)\<in>r" using `x\<in>A` `x \<noteq> a` `minimo A a r`
        by(unfold minimo_def, auto)
      hence "a\<in>A"  using  `minimo A a r` by(unfold minimo_def, auto)
      thus "a\<in>predecesores_de A x r" using `(a,x)\<in>r`
        by(unfold predecesores_de_def, auto)
    qed
  qed
qed

lemma contenencia_orden_estricto:
  assumes "orden_parcial_estricto_en A r" and "B\<subseteq>A"
  shows "orden_parcial_estricto_en B r"
proof-
  have  "irrefl_en A r" and "trans_en A r"
    using  `orden_parcial_estricto_en A r`
    by(unfold orden_parcial_estricto_en_def, auto)
  have 1: "irrefl_en B r"
  proof(unfold irrefl_en_def)
    show "\<forall>x\<in>B. (x, x) \<notin> r"
    proof
      fix x
      assume "x\<in>B"
      hence "x\<in>A" using  `B\<subseteq>A` by auto
      thus "(x,x)\<notin>r" using  `irrefl_en A r`
        by (unfold irrefl_en_def, auto)
    qed
  qed
  have 2:  "trans_en B r"
  proof(unfold trans_en_def)
    show "\<forall>x\<in>B. \<forall>y\<in>B. \<forall>z\<in>B. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
    proof
      fix x assume "x\<in>B"
      show "\<forall>y\<in>B. \<forall>z\<in>B. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
      proof
        fix y  assume "y\<in>B"
        show "\<forall>z\<in>B. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
        proof
          fix z  assume "z\<in>B"
          show "(x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r"
          proof(rule impI)
            assume hip: "(x, y) \<in> r \<and> (y, z) \<in> r"
            show "(x, z) \<in> r"
          proof-
            have "x\<in>A" and  "y\<in>A" and  "z\<in>A" using `x\<in>B` `y\<in>B` `z\<in>B` `B\<subseteq>A`
              by auto
            thus "(x, z) \<in> r" using hip `trans_en A  r` by(unfold trans_en_def, blast)
            qed
          qed
        qed
      qed
    qed
  qed
  thus "orden_parcial_estricto_en B r"
    using 1 2  by(unfold orden_parcial_estricto_en_def, auto)
qed

lemma contenencia_orden_total:
  assumes "total_en A r" and  "B\<subseteq>A"
  shows "total_en B r"
proof(unfold total_en_def)
  show  "\<forall>x\<in>B. \<forall>y\<in>B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
  proof
    fix x
    assume "x\<in>B" show " \<forall>y\<in>B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
    proof
      fix y
      assume "y\<in>B"
      show  "x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
      proof(rule impI)
        assume  "x \<noteq> y"
        show "(x, y) \<in> r \<or> (y, x) \<in> r"
        proof-
          have "x\<in>A \<and> y\<in>A" using  `x\<in>B`  `y\<in>B` `B\<subseteq>A` by auto
          thus  "(x, y) \<in> r \<or> (y, x) \<in> r"
            using  `x \<noteq> y` `total_en A r` by(unfold total_en_def, auto)
        qed
      qed
    qed
  qed
qed

definition maximo ::  "'a set \<Rightarrow> 'a \<Rightarrow>'a rel \<Rightarrow> bool"
  where "maximo A a r \<equiv>  (a\<in>A \<and> (\<forall>x\<in>A. x \<noteq> a \<longrightarrow> (x,a) \<in> r))"

lemma maximo_orden_estricto:
  assumes "orden_parcial_estricto_en A r" and "A\<noteq>{}" and "total_en A r"
  and "finite A"
  shows "(\<exists>a. maximo A a r)"
proof-
  have "orden_parcial_estricto_en A r \<Longrightarrow> A\<noteq>{} \<Longrightarrow> total_en A r \<Longrightarrow> finite A
  \<Longrightarrow> (\<exists>a. maximo A a r)"  using assms(4)
  proof(induct A rule:finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert x A)
    show "(\<exists>a. maximo (insert x A) a r)"
  proof(cases "A={}")
    case True
    hence "insert x A ={x}" by simp
    hence  "maximo (insert x A) x r" by(unfold maximo_def, auto)
    then show ?thesis by auto
  next
    case False
    assume "A \<noteq> {}"
    show "\<exists>a. maximo (insert x A) a r"
    proof-
      have 1: "orden_parcial_estricto_en A r"
        using insert(4) contenencia_orden_estricto by auto
      have 2: "total_en A r" using insert(6) contenencia_orden_total by auto
      have "\<exists>a. maximo A a r" using 1  `A\<noteq>{}`  insert(1) 2 insert(3) by auto
      then obtain a where a: "maximo A a r" by auto
      hence  "a\<in>A" and "\<forall>y\<in>A. y \<noteq> a  \<longrightarrow> (y,a) \<in> r" by(unfold maximo_def, auto)
      have 3: "a\<in>(insert x A)" using `a\<in>A`  by auto
      have 4: "a\<noteq>x" using `a\<in>A` and  `x \<notin> A` by auto
      have  "x\<in>(insert x A)" by auto
      hence "(a,x)\<in>r \<or> (x,a)\<in>r" using 3 4 `total_en (insert x A) r`
        by(unfold total_en_def, auto)
      thus "\<exists>a. maximo (insert x A) a r"
      proof(rule disjE)
        have  "trans_en (insert x A) r" using  insert(4)
          by(unfold orden_parcial_estricto_en_def, auto)
        assume casoa: "(a, x) \<in> r"
        have  "\<forall>z\<in>(insert x A). z \<noteq> x  \<longrightarrow> (z,x) \<in> r"
        proof
          fix z
          assume hip1: "z \<in> (insert x A)"
          show "z \<noteq> x \<longrightarrow> (z, x) \<in> r"
          proof(rule impI)
            assume "z \<noteq> x"
            hence hip2:  "z\<in>A" using `z \<in> (insert x A)` by auto
            thus "(z, x) \<in> r"
            proof(cases)
              assume "z=a"
              thus "(z, x) \<in> r" using `(a, x) \<in> r` by auto
            next
              assume "z\<noteq>a"
              hence "(z,a) \<in> r" using  `z\<in>A` `\<forall>y\<in>A. y \<noteq> a  \<longrightarrow> (y,a) \<in> r` by auto
              have "a\<in>(insert x A)" and "z\<in>(insert x A)" and  "x\<in>(insert x A)"
                using  `a\<in>A` `z\<in>A` by auto
              thus  "(z, x) \<in> r"
                using  `(z,a) \<in> r` `(a, x) \<in> r`  `trans_en (insert x A) r`
                by(unfold trans_en_def, blast)
            qed
          qed
        qed
        thus "\<exists>a. maximo (insert x A) a r"
          using  `x\<in>(insert x A)` by(unfold maximo_def, auto)
      next
        assume casob: "(x, a) \<in> r"
        have  "\<forall>z\<in>(insert x A). z \<noteq> a  \<longrightarrow> (z,a) \<in> r"
        proof
          fix z
          assume hip1: "z \<in> (insert x A)"
          show "z \<noteq> a \<longrightarrow> (z, a) \<in> r"
          proof(rule impI)
            assume "z \<noteq> a" show  "(z, a) \<in> r"
            proof-
              have "z\<in>A \<or> z=x" using `z \<in> (insert x A)` by auto
              thus  "(z, a) \<in> r"
              proof(rule disjE)
                assume  "z \<in> A"
                thus  "(z, a) \<in> r"
                  using  `z \<noteq> a` `\<forall>y\<in>A. y \<noteq> a  \<longrightarrow> (y,a) \<in> r` by auto
              next
                assume "z = x"
                thus  "(z, a) \<in> r" using `(x, a) \<in> r` by auto
              qed
            qed
          qed
        qed
        thus "\<exists>a. maximo (insert x A) a r"
          using `a\<in>(insert x A)`  by(unfold maximo_def, auto)
      qed
    qed
  qed
qed
  thus ?thesis using assms by auto
qed

lemma finito_union:
  fixes S :: "'a  \<Rightarrow>  'a set"
  assumes "\<forall>x. finite (S x)" and "finite A"
  shows "finite (\<Union>a\<in>A. (S a))" using assms by auto

lemma niveles_distintos:
  assumes "k>0"
  shows "(nivel A r n) \<inter> (nivel A r (n+k)) = {}"
proof(rule ccontr)
  assume  "nivel A r n \<inter> nivel A r (n + k) \<noteq> {}"
  hence  "\<exists>x. x\<in>(nivel A r n) \<inter> nivel A r (n + k)" by auto
  then obtain x where "x\<in>(nivel A r n) \<inter> nivel A r (n + k)" by auto
  hence "x\<in>A \<and> altura A x r = n" and "x\<in>A \<and> altura A x r = n+k"
    by(unfold nivel_def, auto)
  thus False using `k>0` by auto
qed

lemma niveles_distintosa:
  assumes "n\<noteq>m"
  shows "(nivel A r n) \<inter> (nivel A r m) = {}"
proof-
  have "n < m \<or> m < n" using assms by auto
  thus ?thesis
  proof(rule disjE)
    assume "n < m"
    hence "\<exists>k. k>0 \<and> m=n+k" by arith
    thus ?thesis using niveles_distintos[of _ A r] by auto
  next
    assume "m < n"
    hence "\<exists>k. k>0 \<and> n=m+k" by arith
    thus ?thesis using  niveles_distintos[of _ A r] by auto
  qed
qed

definition arbol ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "arbol A r  \<equiv>
 r \<subseteq> A \<times> A \<and> r\<noteq>{} \<and> (orden_parcial_estricto_en A r)  \<and>  (\<exists>a. minimo A a r) \<and>
 (\<forall>a\<in>A. finite (predecesores_de A a r) \<and> (total_en (predecesores_de A  a r) r))"

definition arbol_finito::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where
"arbol_finito A r  \<equiv> arbol A r \<and> finite A"

abbreviation  arbol_infinito::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where
"arbol_infinito A r  \<equiv>  arbol A r \<and> \<not> finite A"

definition arbol_enumerable :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"  where
 "arbol_enumerable A r \<equiv> \<exists>g. enumeracion (g:: nat \<Rightarrow>'a)"

definition ramificacion_finita ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where  "ramificacion_finita  A r \<equiv> (\<forall>x\<in>A. finite (sucesores_inmed_de A x r))"

definition sub_orden_lineal_en :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "sub_orden_lineal_en B A r  \<equiv>  B\<subseteq>A \<and> (orden_parcial_estricto_en A r) \<and> (total_en B r)"

definition rama ::  "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "rama  B A r  \<equiv>
 (sub_orden_lineal_en B A r) \<and>
 (\<forall>C. B \<subseteq> C \<and> sub_orden_lineal_en C A r \<longrightarrow> B = C)"

definition rama_finita:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "rama_finita B A r \<equiv>  rama  B A r \<and> finite B"

definition rama_infinita:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "rama_infinita B A r \<equiv>  rama  B A r \<and>  \<not> finite B"

lemma arbol:
  assumes "arbol A r"
  shows
  "r \<subseteq> A \<times> A" and "r\<noteq>{}"
  and  "orden_parcial_estricto_en A r"
  and  "\<exists>a. minimo A a r"
  and  "(\<forall>a\<in>A. finite (predecesores_de A a r) \<and> (total_en (predecesores_de A  a r) r))"
  using `arbol A r` by(unfold arbol_def, auto)

lemma no_vacio:
  assumes "arbol A r" shows "A\<noteq>{}"
proof-
  have "\<exists>a. minimo A a r" using  `arbol A r` arbol[of A r] by auto
  hence "\<exists>a. a\<in>A"  by(unfold minimo_def, auto)
  thus  "A\<noteq>{}" by auto
qed

lemma orden_estricto_pred:
  assumes "arbol A r"
  shows  "\<forall>x\<in>A. orden_parcial_estricto_en (predecesores_de A x r) r"
proof-
  have "irrefl_en A r" and "trans_en A r"  using `arbol A r`
    by(unfold arbol_def,unfold orden_parcial_estricto_en_def,auto)
  thus ?thesis
proof(unfold orden_parcial_estricto_en_def)
  show "\<forall>x\<in>A. irrefl_en (predecesores_de A x r) r \<and>
        trans_en (predecesores_de A x r) r"
  proof
    fix x
    assume "x\<in>A"
    show "irrefl_en (predecesores_de A x r) r \<and> trans_en (predecesores_de A x r) r"
    proof-
      have 1: "irrefl_en (predecesores_de A x r) r"
      proof(unfold irrefl_en_def)
        show "\<forall>y\<in>(predecesores_de A x r). (y, y) \<notin> r"
        proof
          fix y
          assume "y\<in>(predecesores_de A x r)"
          hence "y\<in>A" by(unfold predecesores_de_def,auto)
          thus "(y, y) \<notin> r" using `irrefl_en A r` by(unfold irrefl_en_def,auto)
        qed
      qed
      have 2: "trans_en (predecesores_de A x r) r"
      proof(unfold trans_en_def)
        let ?B= "(predecesores_de A x r)"
        show "\<forall>w\<in>?B. \<forall>y\<in>?B. \<forall>z\<in>?B. (w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
        proof
          fix w assume "w\<in>?B"
         show "\<forall>y\<in>?B. \<forall>z\<in>?B. (w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
         proof
           fix y assume "y\<in>?B"
           show "\<forall>z\<in>?B. (w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
           proof
             fix z  assume "z\<in>?B"
             show "(w, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (w, z) \<in> r"
             proof(rule impI)
               assume hip: "(w, y) \<in> r \<and> (y, z) \<in> r"
               show "(w, z) \<in> r"
               proof-
                 have  "w\<in>A" and  "y\<in>A" and  "z\<in>A" using `w\<in>?B` `y\<in>?B` `z\<in>?B`
                   by(unfold predecesores_de_def,auto)
                 thus "(w, z) \<in> r"
                   using hip `trans_en A  r` by(unfold trans_en_def, blast)
                 qed
               qed
             qed
           qed
         qed
       qed
       show
        "irrefl_en (predecesores_de A x r) r \<and> trans_en (predecesores_de A x r) r"
       using 1 2 by auto
       qed
     qed
  qed
qed

lemma maximo_predecesores:
  assumes "arbol A r" and  "minimo A a r"
  shows "\<forall>x\<in>A. x\<noteq>a \<longrightarrow> (\<exists>b. maximo (predecesores_de A x r) b r)"
proof
  fix x
  assume "x\<in>A"
  show "x\<noteq>a \<longrightarrow> (\<exists>b. maximo (predecesores_de A x r) b r)"
  proof(rule impI)
    assume "x\<noteq>a"
    show "(\<exists>b. maximo (predecesores_de A x r) b r)"
    proof-
      have 1: "orden_parcial_estricto_en (predecesores_de A x r) r"
        using  `arbol A r` `x\<in>A`  orden_estricto_pred by auto
      have 2: "total_en (predecesores_de A x r) r" and
           3: "finite (predecesores_de A x r)" and  "r \<subseteq> A \<times> A"
        using  `arbol A r` `x\<in>A` by(unfold arbol_def, auto)
      have 4:  "(predecesores_de A x r)\<noteq>{}"
        using  `r \<subseteq> A \<times> A`  `minimo A a r`  `x\<in>A`  `x\<noteq>a`
               minimo_predecesor[of A a] by auto
      have 5: "A\<noteq>{}" using `arbol A r` no_vacio by auto
      show "(\<exists>b. maximo (predecesores_de A x r) b r)"
        using 1 2 3 4 5  maximo_orden_estricto by auto
    qed
  qed
qed

lemma pertenece_conjunto:
  assumes  "arbol A r"  and  "card (predecesores_de A x r) = n+1"
  shows  "x\<in>A"
proof-
  have  "r \<subseteq> A \<times> A"  using `arbol A r` by(unfold arbol_def, auto)
  have "(predecesores_de A x r) \<noteq> {}" using assms(2) by auto
  hence "\<exists>y\<in>A. (y,x)\<in>r" by (unfold predecesores_de_def,auto)
  thus  "x\<in>A" using  `r \<subseteq> A \<times> A` by auto
qed

lemma predecesor_inmediato:
  assumes  "arbol A r"
  and  "card (predecesores_de A x r) = n+1" and
  "maximo (predecesores_de A x r) b r"
  shows "altura A b r = n"
proof-
  have "trans_en A r" and  "r \<subseteq> A \<times> A" and  "irrefl_en A r"
    using `arbol A r`
    by (unfold arbol_def, unfold orden_parcial_estricto_en_def, auto)
  have  "x\<in>A" using  assms(1) assms(2)  pertenece_conjunto by auto
  have "orden_parcial_estricto_en (predecesores_de A x r) r"
    using `x\<in>A` `arbol A r` orden_estricto_pred[of A r] by auto
  hence  "irrefl_en (predecesores_de A x r) r" and
          "trans_en (predecesores_de A x r) r"
    by(unfold orden_parcial_estricto_en_def, auto)
  have "b\<in>(predecesores_de A x r)"
    using `maximo (predecesores_de A x r) b r` by(unfold maximo_def, auto)
  have "total_en (predecesores_de A x r) r"
    using `x\<in>A` `arbol A r` by(unfold arbol_def, auto)
  have "card (predecesores_de A x r)>0 " using assms(2) by auto
  hence 1: "finite (predecesores_de A x r)"  using card_gt_0_iff by blast
  have 2: "b\<in>(predecesores_de A x r)"
    using assms(3) by (unfold maximo_def,auto)
  hence "card ((predecesores_de A x r)-{b}) = n"
    using 1  assms(2)  `card (predecesores_de A x r) = n+1`
    card_Diff_singleton[of "(predecesores_de A x r)" b] by auto
  have "(predecesores_de A b r) = ((predecesores_de A x r)-{b})"
  proof(rule equalityI)
    show "(predecesores_de A b r) \<subseteq> (predecesores_de A x r - {b})"
    proof
      fix y
      assume  "y\<in> (predecesores_de A b r)"
      hence "y\<in>A" and  "(y,b)\<in> r" by (unfold predecesores_de_def,auto)
      hence "y\<noteq>b" using `irrefl_en A r` by(unfold irrefl_en_def,auto)
      have "(b,x)\<in>r" using 2 by (unfold predecesores_de_def,auto)
      hence "b\<in>A"  using `r \<subseteq> A \<times> A` by auto
      have "(y,x)\<in> r" using `x\<in>A` `y\<in>A` `b\<in>A`  `(y,b)\<in> r`  `(b,x)\<in>r` `trans_en A r`
        by(unfold trans_en_def, blast)
      show "y\<in>(predecesores_de A x r - {b})"
        using `y\<in>A` `(y,x)\<in> r` `y\<noteq>b` by(unfold predecesores_de_def, auto)
    qed
  next
    show "(predecesores_de A x r - {b}) \<subseteq> (predecesores_de A b r)"
    proof
      fix y
      assume hip: "y\<in>(predecesores_de A x r - {b})"
      hence "y\<noteq>b" and  "y\<in>A" by(unfold predecesores_de_def, auto)
      have "(y,b)\<in> r" using hip `maximo (predecesores_de A x r) b r`
        by(unfold maximo_def,auto)
      thus "y\<in> (predecesores_de A b r)" using `y\<in>A`
        by(unfold predecesores_de_def, auto)
    qed
  qed
  hence 3:  "card (predecesores_de A b r) = card (predecesores_de A x r - {b})"
    by auto
  have "finite (predecesores_de A x r)" using `x\<in>A` `arbol A r` by(unfold arbol_def,auto)
  hence "card (predecesores_de A x r - {b}) = card (predecesores_de A x r)-1 "
    using 2  card_Suc_Diff1 by auto
  hence "card (predecesores_de A b r) = n"
    using 3  `card (predecesores_de A x r) = n+1` by auto
  thus "altura A b r = n" by (unfold altura_def, auto)
qed

lemma altura:
  assumes  "arbol A r" and "altura A x r = n+1"
  shows "\<exists>y. (y,x)\<in>r \<and> altura A y r = n"
proof -
  have 1: "card (predecesores_de A x r) = n+1"
    using assms(2) by (unfold altura_def, auto)
  have "\<exists>a. minimo A a r" using `arbol A r` by(unfold arbol_def, auto)
  then obtain a where a: "minimo A a r"  by auto
  have  "orden_parcial_estricto_en A r" using  `arbol A r` arbol[of A r]  by auto
  hence  "altura  A a r = 0" using a  altura_minimo[of A r] by auto
  hence "x \<noteq> a" using assms(2) by auto
  have "x\<in>A"  using `arbol A r`  1  pertenece_conjunto by auto
  hence "(\<exists>b. maximo (predecesores_de A x r) b r)"
    using `x \<noteq> a` `arbol A r` a maximo_predecesores[of A r a] by auto
  then obtain b where b: "(maximo (predecesores_de A x r) b r)" by auto
  hence "(b,x)\<in>r" by(unfold maximo_def, unfold predecesores_de_def,auto)
  thus "\<exists>y. (y,x)\<in>r \<and> altura A y r = n"
    using  `arbol A r` 1 b predecesor_inmediato[of A r] by auto
qed

lemma nivel:
  assumes  "arbol A r" and "x\<in> (nivel A r (n+1))"
  shows "\<exists>y. (y,x)\<in>r \<and> y \<in> (nivel A r n)"
proof-
  have "altura A x r = n+1"
    using `x\<in> (nivel A r (n+1))` by (unfold nivel_def, auto)
  hence "\<exists>y. (y,x)\<in>r \<and> altura A y r = n"
    using `arbol A r` altura[of A r] by auto
  then obtain y where y:  "(y,x)\<in>r \<and> altura A y r = n" by auto
  have  "r \<subseteq> A \<times> A"  using `arbol A r` by(unfold arbol_def,auto)
  hence "y\<in>A" using y by auto
  hence "(y,x)\<in>r \<and> y \<in> (nivel A r n)" using y by(unfold nivel_def, auto)
  thus ?thesis by auto
qed
(*Para demostrar que en un árbol de ramificación los niveles son finitos, se define
la siguiente función. *)
primrec nivel1 ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow>'a set" where
"nivel1 A r 0 = {a. (minimo A a r)}"
| "nivel1 A r (Suc n)  = (\<Union>a\<in> (nivel1 A r n). sucesores_inmed_de A a r)"

lemma nivel1_cero:
  assumes  "orden_parcial_estricto_en A r" and  "minimo A a r"
  shows "(nivel1 A r 0) = {a}"
proof-
  have "a\<in>(nivel1 A r 0)" using `minimo A a r` by auto
  hence 1: "{a} \<subseteq> (nivel1 A r 0)" by auto
  have 2:  "(nivel1 A r 0) \<subseteq> {a}"
  proof
    {fix x
    assume "x\<in>(nivel1 A r 0)"
    hence "minimo A x r" by auto
    hence "x=a" using assms  unico_minimo[of A r] by auto
    thus "x\<in>{a}" by auto}
  qed
  thus "(nivel1 A r 0) = {a}" using 1 2 by auto
qed

lemma altura_nivel:
  assumes "orden_parcial_estricto_en A r"  and  "minimo A a r"
  and "x \<in> nivel1 A r n"
  shows "altura A x r = n"
proof-
  have
 "\<lbrakk>orden_parcial_estricto_en A r; minimo A a r; x \<in> nivel1 A r n\<rbrakk> \<Longrightarrow>
  altura A x r = n"
  proof(induct n arbitrary: x)
    case 0
    then show "altura A x r = 0"
    proof-
      have "minimo A x r"  using `x \<in> nivel1 A r 0` by auto
      thus "altura A x r = 0"
        using `orden_parcial_estricto_en A r`  altura_minimo[of A r]
        by auto
    qed
  next
    case (Suc n)
    then show ?case
    proof-
      have  "x\<in> (\<Union>a \<in> (nivel1 A r n). (sucesores_inmed_de A a r))"
        using Suc(4) by auto
      then  obtain a
        where hip1:  "a \<in> (nivel1 A r n)" and hip2: "x\<in> (sucesores_inmed_de A a r)"
        by auto
      hence 1: "altura A a r = n" using  Suc(1-3) by auto
      have "altura A x r = (altura A a r)+1"
        using hip2 by(unfold sucesores_inmed_de_def, auto)
      thus "altura A x r = Suc n" using 1 by auto
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma igual_niveles:
  assumes  "arbol A r"
  shows "nivel1 A r n = nivel A r n"
proof(induct n)
  have 1: "orden_parcial_estricto_en A r" and
       2: "\<forall>x\<in>A. finite (predecesores_de A x r)"
    using  `arbol A r` arbol[of A r] by auto
  have "\<exists>a. minimo A a r" using `arbol A r` by(unfold arbol_def, auto)
  then obtain a where a: "minimo A a r"  by auto
  case 0
  then show  "nivel1 A r 0 = nivel A r 0"
  proof-
    have "nivel1 A r 0 = {a}" using 1 a  nivel1_cero[of A r] by auto
    moreover
    have "nivel A r 0 = {a}" using 1 2  a  nivel_cero[of A r] by auto
    ultimately
    show "nivel1 A r 0 = nivel A r 0" by auto
  qed
  next
    case (Suc n)
    assume  "nivel1 A r n = nivel A r n"
    show "nivel1 A r (Suc n) = nivel A r (Suc n)"
    proof(rule equalityI)
      show "nivel1 A r (Suc n) \<subseteq> nivel A r (Suc n)"
      proof(rule subsetI)
        fix x
        assume hip:  "x \<in> nivel1 A r (Suc n)" show "x \<in> nivel A r (Suc n)"
        proof-
          have
          "nivel1 A r (Suc n) = (\<Union>a \<in> (nivel1 A r n). (sucesores_inmed_de A a r))"
            by simp
          hence "x\<in> (\<Union>a \<in> (nivel1 A r n). (sucesores_inmed_de A a r))"
            using hip by auto
          then obtain a where hip1: "a \<in> (nivel1 A r n)" and
            hip2:"x\<in> (sucesores_inmed_de A a r)" by auto
          have "(a,x)\<in>r \<and>  altura A x r = (altura A a r)+1"
            using hip2 by(unfold sucesores_inmed_de_def, auto)
          moreover
          have "\<exists>b. minimo A b r" using `arbol A r` by(unfold arbol_def, auto)
         then obtain b where b: "minimo A b r"  by auto
         have 1:  "r \<subseteq> A \<times> A" and  "orden_parcial_estricto_en A r"
           using `arbol A r` by(unfold arbol_def, auto)
         hence "altura A a r = n" using b hip1  altura_nivel[of A r] by auto
         ultimately
         have "(a,x)\<in>r \<and> altura A x r = n+1" by auto
         hence "x\<in>A \<and> altura A x r = n+1" using `r \<subseteq> A \<times> A` by auto
         thus "x \<in> nivel A r (Suc n)" by(unfold nivel_def, auto)
       qed
     qed
  next
    show "nivel A r (Suc n) \<subseteq> nivel1 A r (Suc n)"
    proof(rule subsetI)
      fix x
      assume hip: "x \<in> nivel A r (Suc n)" show "x \<in> nivel1 A r (Suc n)"
      proof-
        have  1: "x\<in>A \<and> altura A x r = n+1" using hip by(unfold nivel_def,auto)
        hence  "\<exists>y. (y,x)\<in>r \<and> altura A y r = n"
        using assms altura[of A r] by auto
        then obtain y where y1: "(y,x)\<in>r"  and y2: "altura A y r = n" by auto
        hence "x \<in> (sucesores_inmed_de A y r)"
          using 1 by(unfold sucesores_inmed_de_def, auto)
        moreover
        have  "r \<subseteq> A \<times> A"  using `arbol A r` by(unfold arbol_def, auto)
        have "y\<in>A" using y1  `r \<subseteq> A \<times> A` by auto
        hence "y\<in> nivel A r n" using y2 by(unfold nivel_def, auto)
        hence "y\<in> nivel1 A r n" using Suc by auto
        ultimately
        show "x \<in> nivel1 A r (Suc n)" by auto
      qed
    qed
  qed
qed

lemma pertenece_nivel:
  assumes "x \<in> nivel1 A r n"
  shows "x\<in>A"
proof-
  have "x \<in> nivel1 A r n \<Longrightarrow> x\<in>A"
  proof(induct n)
    case 0
    show  "x \<in> A"  using  `x \<in> nivel1 A r 0` minimo_def[of A x r] by auto
  next
    case (Suc n)
    then show "x \<in> A"
    proof-
      have "\<exists>a \<in> (nivel1 A r n). x\<in> sucesores_inmed_de A a r"
        using `x \<in> nivel1 A r (Suc n)` by auto
      then obtain a  where  a1:  "a \<in> (nivel1 A r n)" and
        a2: "x\<in> sucesores_inmed_de A a r" by auto
      show "x \<in> A" using a2 sucesores_inmed_de_def[of A a r] by auto
    qed
  qed
  thus "x \<in> A" using assms by auto
qed

lemma finito_nivel1a:
  assumes  "\<forall>x\<in>A. finite (sucesores_inmed_de A x r)" and "finite (nivel1 A r n)"
  shows "finite (\<Union>a\<in> (nivel1 A r n). sucesores_inmed_de A a r)"
proof
  show "finite (nivel1 A r n)" using assms(2) by simp
next
  fix x
  assume hip:  "x \<in> nivel1 A r n" show  "finite (sucesores_inmed_de A x r)"
  proof-
    have "x\<in>A" using hip  pertenece_nivel[of x A r]  by auto
    thus  "finite (sucesores_inmed_de A x r)"  using assms(1) by auto
  qed
qed

lemma finito_nivel1:
  assumes "finite (nivel1 A r 0)" and  "ramificacion_finita A r"
  shows  "finite (nivel1 A r n)"
proof(induct n)
  case 0
  show "finite (nivel1 A r 0)" using assms  by auto
next
  case (Suc n)
  then show ?case
  proof -
    have 1: "\<forall>x\<in>A. finite (sucesores_inmed_de A x r)"
      using assms by (unfold ramificacion_finita_def, auto)
    hence  "finite (\<Union>a\<in> (nivel1 A r n). sucesores_inmed_de A a r)"
      using Suc(1) finito_nivel1a[of A r] by auto
    thus "finite (nivel1 A r (Suc n))" by auto
  qed
qed

lemma finito_nivel:
  assumes  "arbol A r" and "ramificacion_finita  A r"
  shows  "finite (nivel A r n)"
proof-
  have 1: "orden_parcial_estricto_en A r"  using `arbol A r` arbol[of A r] by auto
  have  "\<exists>a. minimo A a r"  using `arbol A r` arbol[of A r] by auto
  then obtain a where "minimo A a r" by auto
  hence "finite (nivel1 A r 0)"
    using 1  nivel1_cero[of A r] by auto
  hence "finite (nivel1 A r n)"
    using `ramificacion_finita  A r` finito_nivel1[of A r] by auto
  thus  ?thesis using `arbol A r` igual_niveles[of A r n] by auto
qed

lemma  finito_nivel_a:
  assumes "arbol A r" and "\<forall>n. finite (nivel A r n)"
  shows "ramificacion_finita A r"
proof(unfold ramificacion_finita_def)
  show  "\<forall>x\<in>A. finite (sucesores_inmed_de A x r)"
  proof
  fix x
  assume "x\<in>A"
  show "finite (sucesores_inmed_de A x r)" using ramificacion_finita_def
  proof-
    let ?n = "(altura A x r)"
    have "(sucesores_inmed_de A x r) \<subseteq> (nivel A r (?n+1))"
      using sucesores_inmed_de_def[of A x r] nivel_def[of A r "?n+1"] by auto
    thus "finite (sucesores_inmed_de A x r)"  using assms(2) by(simp add: finite_subset)
  qed
qed
qed

lemma vacio_predec:
  assumes "\<forall>x\<in>A. (x,y)\<notin>r"
  shows "predecesores_de A y r ={}"
    using assms by(unfold predecesores_de_def, auto)

lemma nivel_elemento:
 "\<forall>x\<in>A.\<exists>n. x\<in> nivel A r n"
proof
  fix x
  assume hip: "x\<in>A" show "\<exists>n. x \<in> nivel A r n"
  proof-
    let ?n = "altura A x r"
    have "x\<in>nivel A r ?n" using `x\<in>A`  by (unfold nivel_def, auto)
    thus "\<exists>n. x \<in> nivel A r n" by auto
  qed
qed

lemma union_niveles:
  shows "A =(\<Union>n. nivel A r n)"
proof(rule equalityI)
  show "A \<subseteq> (\<Union>n. nivel A r n)"
  proof(rule subsetI)
    fix x
    assume hip: "x\<in>A" show "x\<in>(\<Union>n. nivel A r n)"
    proof-
      have "\<exists>n. x\<in> nivel A r n"
        using hip nivel_elemento[of A] by auto
      then obtain n where  "x\<in> nivel A r n" by auto
    thus ?thesis by auto
  qed
qed
next
  show  "(\<Union>n. nivel A r n) \<subseteq> A"
  proof(rule subsetI)
    fix x
    assume hip:  "x \<in> (\<Union>n. nivel A r n)" show "x \<in> A"
    proof-
      obtain n where  "x\<in> nivel A r n" using hip by auto
      thus "x \<in> A" by(unfold nivel_def, auto)
    qed
  qed
qed

lemma camino1:
  assumes  "arbol A r"  and  "x \<in> (nivel A r (n+1))"
  shows "\<forall>k.(0\<le>k \<and> k\<le>n)\<longrightarrow> (\<exists>y. (y,x)\<in>r \<and> y \<in> (nivel A r k))"
proof-
  have "arbol A r \<Longrightarrow> x \<in> (nivel A r (n+1)) \<Longrightarrow>
  \<forall>k.(0\<le>k \<and> k\<le>n)\<longrightarrow> (\<exists>y. (y,x)\<in>r \<and> y \<in> (nivel A r k))"
  proof(induction n arbitrary: x)
    have "r \<subseteq> A \<times> A" and 1:  "orden_parcial_estricto_en A r"
    and "\<exists>a. minimo A a r"
    and 2: "\<forall>x\<in>A. finite (predecesores_de A x r)"
      using `arbol A r` arbol[of A r] by auto
    case 0
    show  "\<forall>k. 0 \<le> k \<and> k \<le> 0 \<longrightarrow> (\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
    proof
      fix k
      show "0 \<le> k \<and> k \<le> 0 \<longrightarrow> (\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
      proof(rule impI)
        assume hip:  "0 \<le> k \<and> k \<le> 0"
        show "(\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
        proof-
          have "k=0" using hip  by auto
          thus "(\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
            using `arbol A r`  `x \<in> (nivel A r (0 + 1))` nivel[of A r ]  by auto
        qed
      qed
    qed
    next
      case (Suc n)
      show "\<forall>k. 0 \<le> k \<and> k \<le> Suc n \<longrightarrow> (\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
  proof(rule allI, rule impI)
    fix k
    assume hip:  "0 \<le> k \<and> k \<le> Suc n"
    show  "(\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
    proof-
      have "(0 \<le> k \<and> k \<le> n) \<or> k = Suc n"  using hip by auto
      thus ?thesis
      proof(rule disjE)
        assume hip1:  "0 \<le> k \<and> k \<le> n"
        have "\<exists>y. (y,x)\<in>r \<and> y \<in> (nivel A r (n+1))"
        using `arbol A r` nivel  `x \<in> nivel A r (Suc n + 1)` by auto
        then obtain y where y1: "(y,x)\<in>r" and y2: "y \<in> (nivel A r (n+1))"
          by auto
        have "\<forall>k. 0 \<le> k \<and> k \<le> n \<longrightarrow> (\<exists>z. (z, y) \<in> r \<and> z \<in> nivel A r k)"
          using y2  Suc(1-3) by auto
        hence "(\<exists>z. (z, y) \<in> r \<and> z \<in> nivel A r k)"
          using hip1 by auto
        then obtain z where  z1: "(z, y) \<in> r" and z2: "z \<in> (nivel A r k)" by auto
        have  "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r"
          using  `arbol A r` arbol by auto
        hence "z\<in>A" and  "y\<in>A" and "x\<in>A"
          using `r \<subseteq> A \<times> A` `(z, y) \<in> r` `(y,x)\<in>r` by auto
        have "trans_en A r" using `orden_parcial_estricto_en A r`
          by(unfold orden_parcial_estricto_en_def, auto)
        hence "(z, x) \<in> r" using `z\<in>A` `y\<in>A` and `x\<in>A` `(z, y) \<in> r` `(y,x)\<in>r`
          by(unfold trans_en_def, blast)
        thus "(\<exists>y. (y, x) \<in> r \<and> y \<in> nivel A r k)"
          using z2 by auto
      next
        assume  "k = Suc n"
        thus  "\<exists>y. (y,x)\<in>r \<and> y \<in> (nivel A r k)"
          using `arbol A r` nivel `x \<in> nivel A r (Suc n + 1)` by auto
        qed
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma nivel1:
  assumes "arbol A r"
  shows "(nivel A r (n+1))\<noteq> {} \<longrightarrow> (\<forall>k.(0\<le>k \<and> k\<le>n) \<longrightarrow> (nivel A r k)\<noteq> {})"
proof(rule impI)
  assume hip:  "(nivel A r (n+1))\<noteq> {}"
    show  "(\<forall>k.(0\<le>k \<and> k\<le>n) \<longrightarrow> (nivel A r k)\<noteq> {})"
    proof-
      have  "\<exists>x. x\<in>(nivel A r (n+1))" using hip by auto
      then obtain x where x: "x\<in>(nivel A r (n+1))" by auto
      thus ?thesis using assms camino1[of A r] by blast
    qed
  qed

lemma nivel2:
  assumes  "arbol A r"
  shows  "((nivel A r (n+1)) = {}) \<longrightarrow> (\<forall>k. k>(n+1) \<longrightarrow> (nivel A r k) = {})"
proof(rule ccontr)
  assume hip: "\<not> (nivel A r (n+1) = {} \<longrightarrow> (\<forall>k>(n+1). nivel A r k = {}))"
  show False
  proof-
    have "((nivel A r (n+1)) = {}) \<and> \<not>(\<forall>k>(n+1). nivel A r k = {})"
      using hip by auto
    hence 1: "(nivel A r (n+1)) = {}" and 2: "\<exists>k>(n+1). (nivel A r k) \<noteq> {}"
      by auto
    obtain z where z1: "z>(n+1)" and z2: "(nivel A r z) \<noteq> {}"
      using 2 by auto
    have "z>0" using  `z>(n+1)` by auto
    hence "(nivel A r ((z-1)+1)) \<noteq> {}"
      using z2 by simp
    hence "\<forall>k.(0\<le>k \<and> k\<le>(z-1)) \<longrightarrow> (nivel A r k)\<noteq> {}"
      using  z2 `arbol A r` nivel1[of A r "z-1"]
      by auto
    hence  "(nivel A r (n+1)) \<noteq> {}"
      using `z>(n+1)` by auto
    thus False using 1 by auto
  qed
qed

lemma arbol_finito1:
  assumes "arbol A r" and "\<forall>k. k>m \<longrightarrow> (nivel A r k) = {}"
  shows "A = (\<Union>n\<in>{0..m}. nivel A r n)"
proof-
  have a: "A = (\<Union>n. nivel A r n)" using  union_niveles[of A r] by auto
  have "(\<Union>n. nivel A r n) = (\<Union>n\<in>{0..m}. nivel A r n)"
  proof(rule equalityI)
    show "(\<Union>n. nivel A r n) \<subseteq> (\<Union>n\<in>{0..m}.  nivel A r n)"
    proof(rule subsetI)
      fix x
      assume hip: "x\<in>(\<Union>n. nivel A r n)"
      show "x\<in>(\<Union>n\<in>{0..m}. nivel A r n)"
      proof-
        have "\<exists>n. x\<in> nivel A r n"
        using hip nivel_elemento[of A] by auto
        then obtain n where n: "x\<in> nivel A r n" by auto
        have "n\<in>{0..m}"
        proof(rule ccontr)
          assume 1: "n \<notin> {0..m}"
          show False
          proof-
            have "n > m" using 1 by auto
            thus False using assms(2) n by auto
          qed
        qed
        thus "x\<in>(\<Union>n\<in>{0..m}. nivel A r n)" using n by auto
      qed
    qed
  next
    show  "(\<Union>n\<in>{0..m}. nivel A r n) \<subseteq> (\<Union>n. nivel A r n)" by auto
  qed
  thus  "A = (\<Union>n\<in>{0..m}. nivel A r n)" using a by auto
qed

lemma arbol_finito:
  assumes "arbol A r"  and  "ramificacion_finita  A r"
  and "\<exists>n. (\<forall>k. k>n \<longrightarrow> (nivel A r k) = {})"
  shows "finite A"
proof-
  obtain m where m: "(\<forall>k. k>m \<longrightarrow> (nivel A r k) = {})"
    using assms(3) by auto
  hence 1: "A =(\<Union>n\<in>{0..m}. nivel A r n)"
    using  assms(1) assms(3) arbol_finito1[of A r m] by auto
  have "\<forall>n. finite (nivel A r n)"
    using assms(1-2) finito_nivel by auto
  hence "\<forall>n\<in>{0..m}. finite (nivel A r n)" by auto
  hence "finite (\<Union>n\<in>{0..m}. nivel A r n)" by auto
  thus "finite A" using 1 by auto
qed

lemma niveles_no_vacios:
  assumes  "arbol_infinito A r" and  "ramificacion_finita A r"
  shows "\<forall>n. nivel A r n \<noteq> {}"
proof(rule ccontr)
  assume hip: "\<not> (\<forall>n. nivel A r n \<noteq> {})"
  show False
  proof-
    have "arbol A r" using `arbol_infinito A r` by auto
    have "(\<exists>n. nivel A r n = {})" using hip by auto
    then obtain n where n: "nivel A r n = {}" by auto
    thus False
    proof(cases n)
      case 0
      then show False
      proof-
        have "\<exists>a. minimo A a r" using `arbol A r` arbol[of A r] by auto
        then obtain a where a:  "minimo A a r" by auto
        have " orden_parcial_estricto_en A r"
        and "\<forall>x\<in>A. finite (predecesores_de A x r)"
          using  `arbol A r` arbol[of A r] by auto
        hence "nivel A r n = {a}"
          using a `n=0` nivel_cero[of A r a] by auto
        thus False using `nivel A r n = {}` by auto
      qed
      next
        case (Suc nat)
        fix m
        assume hip: "n = Suc m" show False
        proof-
          have 1:  "nivel A r (Suc m) = {}"
            using hip  n by auto
        have "(\<forall>k. k>(m+1) \<longrightarrow> (nivel A r k) = {})"
          using `arbol A r` 1  nivel2[of A r m] by auto
        hence 1: "(\<exists>n. \<forall>k. k>n \<longrightarrow> (nivel A r k) = {})" by auto
        hence 2: "finite A"
          using `arbol A r` 1 `ramificacion_finita  A r` arbol_finito[of A r] by auto
        have 3:  "\<not> finite A" using `arbol_infinito A r` by auto
        show False using 2 3 by auto
      qed
    qed
  qed
qed

lemma no_ciclos:
  assumes "arbol A r" and "(x,z)\<in>r" and "(y,z)\<in>r" and "x\<noteq>y"
  shows "(x,y)\<in>r \<or> (y,x)\<in>r"
proof-
  have "r \<subseteq> A \<times> A" using `arbol A r` by(unfold arbol_def, auto)
  hence "x\<in>A" and  "y\<in>A" and  "z\<in>A" using  `(x,z)\<in>r` and `(y,z)\<in>r` by auto
  hence 1: "x \<in> predecesores_de A z r" and 2: "y \<in> predecesores_de A z r"
    using assms by(unfold predecesores_de_def, auto)
  have "(total_en (predecesores_de A  z r) r)"
    using `arbol A r` `z\<in>A` by(unfold arbol_def, auto)
  thus ?thesis using 1 2 `x\<noteq>y`  total_en_def[of "predecesores_de A z r" r] by auto
qed

lemma contenencia_predecesores:
  assumes  "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r" and "(x,y)\<in>r"
  shows "(predecesores_de A x r) \<subset> (predecesores_de A y r)"
proof-
  have "irrefl_en A r" and "trans_en A r"
    using assms(2) by (unfold orden_parcial_estricto_en_def, auto)
  have 1: "(predecesores_de A x r)\<subseteq> (predecesores_de A y r)"
  proof(rule subsetI)
    fix z
    assume "z\<in>predecesores_de A x r"
    hence "z\<in>A" and "(z,x)\<in>r" by(unfold predecesores_de_def, auto)
    have "x\<in>A" and "y\<in>A"  using `(x,y)\<in>r` `r \<subseteq> A \<times> A` by auto
    hence "(z,y)\<in>r"
      using `z\<in>A` `y\<in>A` `x\<in>A` `(z,x)\<in>r` `(x,y)\<in>r` `trans_en A r`
      by (unfold trans_en_def, blast)
    thus "z\<in>predecesores_de A y r"
      using `z\<in>A` by(unfold predecesores_de_def, auto)
  qed
  have 2: "x\<in>predecesores_de A y r"
    using `r \<subseteq> A \<times> A` `(x,y)\<in>r` by(unfold predecesores_de_def, auto)
  have 3:  "x\<notin>predecesores_de A x r"
  proof(rule ccontr)
    assume "\<not> x \<notin> predecesores_de A x r"
    hence "x \<in> predecesores_de A x r" by auto
    hence "x\<in>A \<and> (x,x)\<in>r"
      by(unfold predecesores_de_def, auto)
    thus False using `irrefl_en A r`
      by (unfold irrefl_en_def, auto)
  qed
  have "(predecesores_de A x r) \<noteq> (predecesores_de A y r)"
    using 2 3 by auto
  thus ?thesis using 1 by auto
qed

lemma alturas_diferentes:
  assumes  "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r" and "(x,y)\<in>r"
  and  "finite (predecesores_de A y r)"
  shows "altura A x r < altura A y r"
proof-
  have "card(predecesores_de A x r) < card(predecesores_de A y r)"
    using assms  contenencia_predecesores[of r A x y] psubset_card_mono by auto
  thus ?thesis by(unfold altura_def, auto)
qed

lemma pertenecen_niveles_diferentes:
  assumes  "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r" and "(x,y)\<in>r"
  and "x \<in> (nivel A r n)"  and  "y \<in> (nivel A r m)"
  and  "finite (predecesores_de A y r)"
  shows "nivel A r n \<noteq> nivel A r m"
proof(rule ccontr)
  assume "\<not> nivel A r n \<noteq> nivel A r m"
  hence "nivel A r n = nivel A r m"  by auto
  hence "x \<in> (nivel A r m)"  using `x \<in> (nivel A r n)` by auto
  hence 1:  "altura A x r= m"  by(unfold nivel_def, auto)
  have "altura A y r= m" using `y \<in> (nivel A r m)` by(unfold nivel_def, auto)
  hence "altura A x r = altura A y r" using 1 by auto
  thus False
    using assms alturas_diferentes[of r A x y] by (unfold nivel_def, auto)
qed

lemma altura_predecesor:
  assumes  "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r"
  and "x \<in> predecesores_de A y r"  and "y \<in> (nivel A r n)"
  and  "x \<in> (nivel A r m)"
  and "finite (predecesores_de A y r)"
  shows "m<n"
proof-
  have "(x,y)\<in>r" using `(x \<in> predecesores_de A y r)`
    by (unfold predecesores_de_def, auto)
  thus ?thesis
    using assms  alturas_diferentes[of r A x y] by(unfold nivel_def, auto)
qed

lemma niveles_diferentes_arbol:
  assumes "arbol A r" and "x\<in>(predecesores_de A z r)"
  and "y\<in>(predecesores_de A z r)"
  and  "x\<noteq>y" and "x \<in> (nivel A r n)" and "y \<in> (nivel A r m)"
  shows "nivel A r n \<inter> nivel A r m = {}"
proof-
  have "(x,y)\<in>r \<or> (y,x)\<in>r"
    using assms no_ciclos[of A] by(unfold predecesores_de_def, auto)
  thus "nivel A r n \<inter> nivel A r m ={}"
  proof(rule disjE)
    assume  "(x, y) \<in> r"
    have "r\<subseteq> A \<times> A" and 1: "orden_parcial_estricto_en A r"
      using  `arbol A r` by(unfold arbol_def,auto)
    hence "x\<in>A" and "y\<in>A"  and  2: "x\<in>(predecesores_de A y r)"
      using `(x, y) \<in> r`  by(unfold predecesores_de_def, auto)
    have 3: "finite (predecesores_de A y r)"
      using `y\<in>A`  `arbol A r` by(unfold arbol_def, auto)
    hence  "n<m"
      using assms `r\<subseteq> A \<times> A` 1 2 3 altura_predecesor[of r A x y m n]
      by auto
    hence "\<exists>k>0. m=n+k" by arith
    then obtain k where k: "k>0" and m: "m=n+k" by auto
    thus ?thesis using niveles_distintos[OF k, of A ]
      by auto
  next
    assume  "(y, x) \<in> r"
    have "r\<subseteq> A \<times> A" and 1: "orden_parcial_estricto_en A r"
      using  `arbol A r` by(unfold arbol_def,auto)
    hence "x\<in>A" and "y\<in>A" and 2: "y\<in>(predecesores_de A x r)"
      using `(y, x) \<in> r`
      by(unfold predecesores_de_def, auto)
    have 3: "finite (predecesores_de A x r)"
      using `x\<in>A` `arbol A r`
      by(unfold arbol_def, auto)
    hence  "m<n"
      using assms `r\<subseteq> A \<times> A` 1 2 3 altura_predecesor[of r A y x n m]
      by auto
    hence "\<exists>k>0. n=m+k" by arith
    then obtain k where k: "k>0" and m: "n=m+k" by auto
    thus ?thesis using  niveles_distintos[OF k, of A] by auto
  qed
qed

lemma niveles_diferentes_arbol1:
  assumes "arbol A r" and "(x,z)\<in> r" and "(y,z)\<in> r"
  and  "x\<noteq>y" and  "x \<in> (nivel A r n)" and "y \<in> (nivel A r m)"
shows "nivel A r n \<inter> nivel A r m = {}"
proof-
  have "r \<subseteq> A \<times> A"  using  `arbol A r` arbol by auto
  hence "x\<in>A" and  "y\<in>A"  using  `r \<subseteq> A \<times> A`  `(x,z) \<in> r`  `(y,z)\<in>r` by auto
  hence "x\<in>(predecesores_de A z r)" and "y\<in>(predecesores_de A z r)"
    using  `(x,z)\<in> r` and `(y,z)\<in> r` by(unfold predecesores_de_def, auto)
  thus ?thesis
    using assms  niveles_diferentes_arbol[of A r] by blast
qed

definition conj_a_lista :: "'a set \<Rightarrow> 'a list"
  where "conj_a_lista s =  (SOME l. set l = s)"

lemma  conj_conj_a_list:
   "finite s \<Longrightarrow> set (conj_a_lista s) = s"
  unfolding conj_a_lista_def by (metis (mono_tags) finite_list some_eq_ex)

lemma lista_conjunto:
  assumes "arbol A r" and  "ramificacion_finita A r"
  shows "set (conj_a_lista (nivel A r n)) = (nivel A r n)"
  using assms finito_nivel[of A r n]  conj_conj_a_list by auto

primrec disyuncion_nodos :: "'a list  \<Rightarrow> 'a formula"  where
 "disyuncion_nodos [] = FF"
| "disyuncion_nodos (v#D) = (Atomo v) \<or>. (disyuncion_nodos D)"

lemma valor_verdad_disyuncion_nodos:
  assumes "v\<in> set l" and "valor I (Atomo v) = Verdad"
  shows "valor I (disyuncion_nodos l) = Verdad"
proof-
  have "v\<in> set l \<Longrightarrow> valor I (Atomo v) = Verdad \<Longrightarrow>
  valor I (disyuncion_nodos l) = Verdad"
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    then show  "valor I (disyuncion_nodos (a # l)) = Verdad"
    proof-
      have "v = a \<or> v\<noteq>a" by auto
      thus  "valor I (disyuncion_nodos (a # l)) = Verdad"
      proof(rule disjE)
        assume "v = a"
        hence 1: "disyuncion_nodos (a#l) = (Atomo v) \<or>. (disyuncion_nodos l)"
          by auto
        have "valor I ((Atomo v) \<or>. (disyuncion_nodos l)) = Verdad "
          using Cons(3)  by(unfold valor_def,unfold v_disyuncion_def, auto)
        thus ?thesis using 1  by auto
      next
        assume "v \<noteq> a"
        hence "v\<in> set l" using Cons(2) by auto
        hence "valor I (disyuncion_nodos l) = Verdad "
          using Cons(1) Cons(3) by auto
        thus ?thesis
          by(unfold valor_def,unfold v_disyuncion_def, auto)
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma valor_verdad_disyuncion_formulas:
  assumes  "arbol A r" and  "ramificacion_finita A r"
  and  "v\<in>(nivel A r n) \<and> valor I (Atomo v) = Verdad"
  and  "F = disyuncion_nodos(conj_a_lista (nivel A r n))"
  shows "valor I F = Verdad"
proof-
  have "set (conj_a_lista (nivel A r n)) = (nivel A r n)"
    using lista_conjunto assms(1-2) by auto
  hence "v\<in> set (conj_a_lista (nivel A r n))"
    using assms(3) by auto
  thus "valor I F = Verdad"
    using assms(3-4) valor_verdad_disyuncion_nodos by auto
qed

definition \<F>' :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
   "\<F>' A r  \<equiv> (\<Union>n. {disyuncion_nodos(conj_a_lista (nivel A r n))})"

definition \<G>' ::  "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
   "\<G>' A r \<equiv> {(Atomo u) \<rightarrow>. (Atomo v) |u v. u\<in>A \<and> v\<in>A \<and> (v,u)\<in> r}"

definition \<H>n :: "'a set \<Rightarrow> 'a rel \<Rightarrow> nat \<Rightarrow> ('a formula) set"  where
   "\<H>n A r n \<equiv> {\<not>.((Atomo u) \<and>. (Atomo v))
                         |u v . u\<in>(nivel A r n) \<and> v\<in>(nivel A r n) \<and> u\<noteq>v }"
definition \<H>'  :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
 "\<H>' A r  \<equiv> \<Union>n. \<H>n A r n"

definition \<T>' :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a formula) set"  where
   "\<T>' A r  \<equiv> (\<F>' A r) \<union> (\<G>' A r) \<union> (\<H>' A r)"

primrec nodos_formula :: "'v formula  \<Rightarrow> 'v set" where
  "nodos_formula FF = {}"
| "nodos_formula TT = {}"
| "nodos_formula (Atomo P) =  {P}"
| "nodos_formula (\<not>. F) = nodos_formula F"
| "nodos_formula (F \<and>. G) = nodos_formula F \<union> nodos_formula G"
| "nodos_formula (F \<or>. G) = nodos_formula F \<union> nodos_formula G"
| "nodos_formula (F \<rightarrow>.G) = nodos_formula F \<union> nodos_formula G"

definition nodos_conjunto_formulas :: "'v formula set  \<Rightarrow> 'v set"  where
"nodos_conjunto_formulas S = (\<Union>F\<in> S. nodos_formula F)"

definition maximo_nivel:: "'v set \<Rightarrow>'v rel \<Rightarrow> 'v  formula  set  \<Rightarrow>  nat"  where
 "maximo_nivel A r S =  Max (\<Union>x\<in>nodos_conjunto_formulas S. {altura A x r})"

lemma nodo_formula:
  assumes "v \<in> set l"
  shows "v \<in> nodos_formula (disyuncion_nodos l)"
proof-
  have "v \<in> set l \<Longrightarrow> v \<in> nodos_formula (disyuncion_nodos l)"
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    show "v \<in> nodos_formula (disyuncion_nodos (a # l))"
   proof-
     have "v = a \<or> v\<noteq>a" by auto
     thus "v \<in> nodos_formula (disyuncion_nodos (a # l))"
     proof(rule disjE)
       assume "v = a"
       hence 1: "disyuncion_nodos (a#l) = (Atomo v) \<or>. (disyuncion_nodos l)"
         by auto
       have "v \<in> nodos_formula ((Atomo v) \<or>. (disyuncion_nodos l))" by auto
       thus ?thesis using 1  by auto
     next
       assume "v \<noteq> a"
       hence "v\<in> set l" using Cons(2) by auto
       hence "v \<in> nodos_formula (disyuncion_nodos l)"
         using Cons(1) Cons(2) by auto
       thus ?thesis by auto
     qed
   qed
 qed
  thus ?thesis using assms by auto
qed

lemma nodo_disyuncion_formulas:
  assumes  "arbol A r" and  "ramificacion_finita A r" and "v\<in>(nivel A r n)"
  and  "F = disyuncion_nodos(conj_a_lista (nivel A r n))"
  shows  "v \<in> nodos_formula F"
proof-
  have "set (conj_a_lista (nivel A r n)) = (nivel A r n)"
    using lista_conjunto assms(1-2) by auto
  hence "v\<in> set (conj_a_lista (nivel A r n))"
    using assms(3) by auto
  thus "v \<in> nodos_formula F"
    using assms(3-4)  nodo_formula  by auto
qed

definition nodo_sig_nivel_max:: "'v set \<Rightarrow> 'v rel \<Rightarrow> 'v formula set  \<Rightarrow> 'v"
  where "nodo_sig_nivel_max A r S =
  (SOME u. u \<in> (nivel A r ((maximo_nivel A r S)+1)))"

fun interpretacion_camino :: "'v set \<Rightarrow>'v rel \<Rightarrow> 'v \<Rightarrow> ('v  \<Rightarrow> v_verdad)"  where
"interpretacion_camino A r v = (\<lambda>u. (if (u,v)\<in>r  then Verdad else Falso))"

lemma finito_nodos_formula:
 "finite (nodos_formula F)" by(induct F, auto)

lemma finito_conjunto_nodos:
  assumes "finite S"
  shows  "finite (nodos_conjunto_formulas S)"
  using assms finito_nodos_formula
  by (unfold nodos_conjunto_formulas_def, auto)

lemma nodo_nivel_maximo:
  assumes  "arbol_infinito A r" and  "ramificacion_finita A r"
  shows "\<exists>u. u \<in> (nivel A r ((maximo_nivel A r S)+1))"
    using assms  niveles_no_vacios[of A r] by(unfold nivel_def, auto)

lemma maximo1:
  assumes  "finite S" and "u \<in> nodos_conjunto_formulas S"
  shows "(altura A u r)  \<le> (maximo_nivel A r S)"
proof-
  have "(altura A u r) \<in> ( \<Union>x\<in>nodos_conjunto_formulas S. {altura A x r})"
    using assms(2) by auto
  thus "(altura A u r)  \<le> (maximo_nivel A r S)"
    using `finite S` finito_conjunto_nodos[of S]
    by(unfold maximo_nivel_def, auto)
qed

lemma negacion_implicacion:
  assumes "valor I (F \<rightarrow>.G) = Falso"
  shows "valor I F = Verdad \<and> valor I G = Falso"
proof(rule ccontr)
  assume "\<not> (valor I F = Verdad \<and> valor I G = Falso)"
  hence "valor I F = Falso \<or> valor I G = Verdad"
    using CasosValor by auto
  hence "valor I (F \<rightarrow>.G) = Verdad"
    by(unfold valor_def, unfold v_implicacion_def, auto)
  thus False using assms by auto
qed

lemma valor_interpretacion_camino:
  assumes "valor (interpretacion_camino A r v) (Atomo u) = Verdad"
  shows "(u,v)\<in>r"
proof(rule ccontr)
  assume "(u, v) \<notin> r"
  hence "valor (interpretacion_camino A r v) (Atomo u) = Falso"
    by(unfold valor_def, auto)
  thus False using assms by auto
qed

lemma camino_satisfacible:
  assumes "arbol_infinito A r"
  and  "ramificacion_finita A r" and  "S \<subseteq> (\<T>' A r)"
  and "finite S"
shows  "satisfacible S"
proof-
  let ?m = "(maximo_nivel A r S)+1"
  let ?nivel = "nivel A r ?m"
  let ?u = "nodo_sig_nivel_max A r S"
  let ?F = "Atomo (?u, ?m)"
  have 1: "arbol A r" using `arbol_infinito A r` by auto
  have  "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r"
    using  `arbol A r` arbol by auto
  have "trans_en A r"
    using `orden_parcial_estricto_en A r`
    by(unfold orden_parcial_estricto_en_def, auto)
  have "\<exists>u. u\<in> nivel A r ?m"
    using assms(1-2) nodo_nivel_maximo by auto
  then obtain u where u: "u\<in> nivel A r ?m"  by auto
  hence nivelu:  "?u \<in> nivel A r ?m"
    using someI by (unfold nodo_sig_nivel_max_def,auto)
  hence "?u\<in>A" by(unfold nivel_def, auto)
  have "(interpretacion_camino A r ?u) modelo S"
  proof(unfold modelo_def)
    show "\<forall>F\<in>S. valor (interpretacion_camino A r ?u) F = Verdad"
    proof
      fix F assume "F \<in> S"
      show  "valor (interpretacion_camino A r ?u) F  = Verdad"
      proof-
        have "F \<in> (\<F>' A r) \<union> (\<G>' A r) \<union> (\<H>' A r)"
        using `S \<subseteq>  \<T>' A r` `F \<in> S` assms(2)  by(unfold \<T>'_def,auto)
        hence  "F \<in> (\<F>' A r) \<or> F \<in> (\<G>' A r) \<or> F \<in> (\<H>' A r)" by auto
        thus ?thesis
        proof(rule disjE)
          assume "F \<in> (\<F>' A r)"
          hence "\<exists>n. F = disyuncion_nodos(conj_a_lista (nivel A r n))"
            by(unfold \<F>'_def,auto)
          then obtain n
            where n: "F = disyuncion_nodos(conj_a_lista (nivel A r n))"
            by auto
          have "\<exists>v. v\<in>(nivel A r n)"
            using  assms(1-2) niveles_no_vacios[of A r] by auto
          then obtain v where v: "v \<in> (nivel A r n)" by auto
          hence  "v \<in> nodos_formula F"
            using n nodo_disyuncion_formulas[OF 1 assms(2) v, of F ]
            by auto
          hence a: "v \<in> nodos_conjunto_formulas S"
            using `F \<in> S`  by(unfold nodos_conjunto_formulas_def, blast)
          hence b: "(altura A v r) \<le> (maximo_nivel A r S)"
            using `finite S`  maximo1[of S v] by auto
          have "(altura A v r) = n"
            using v by(unfold nivel_def, auto)
          hence  "n < ?m"
            using `finite S` a   maximo1[of S v A r]
            by(unfold maximo_nivel_def, auto)
          hence "(\<exists>y. (y,?u)\<in>r \<and> y \<in> (nivel A r n))"
            using nivelu `arbol A r` camino1[of A r]
            by auto
          then obtain y where y1: "(y,?u)\<in>r" and y2: "y \<in> (nivel A r n)"
            by auto
          hence "valor (interpretacion_camino A r ?u) (Atomo y) = Verdad"
            by auto
          thus "valor (interpretacion_camino A r ?u) F = Verdad"
            using 1 assms(2) y2 n  valor_verdad_disyuncion_formulas[of A r y]
            by auto
        next
          assume  "F \<in> \<G>' A r \<or> F \<in> \<H>' A r"
          thus "valor (interpretacion_camino A r ?u) F = Verdad"
          proof(rule disjE)
            assume  "F \<in> \<G>' A r"
            hence "\<exists>u. \<exists>v. u\<in>A \<and> v\<in>A  \<and> (v,u)\<in> r  \<and>
                  (F = (Atomo u) \<rightarrow>. (Atomo v))"
              by (unfold  \<G>'_def, auto)
            then obtain u v where "u\<in>A" and "v\<in>A" and "(v,u)\<in> r"
            and F: "(F = (Atomo u) \<rightarrow>. (Atomo v))" by auto
            show "valor (interpretacion_camino A r ?u) F = Verdad"
            proof(rule ccontr)
              assume "\<not>(valor (interpretacion_camino A r ?u) F = Verdad)"
              hence "valor (interpretacion_camino A r ?u) F = Falso"
                using CasosValor by auto
              hence "valor (interpretacion_camino A r ?u) (Atomo u) =  Verdad \<and>
              valor (interpretacion_camino A r ?u) (Atomo v) =  Falso"
                using F  negacion_implicacion by blast
              hence 1: "valor (interpretacion_camino A r ?u) (Atomo u) =  Verdad"
              and   2: "valor (interpretacion_camino A r ?u) (Atomo v) =  Falso"
                by auto
              have "(u,?u)\<in>r" using 1 valor_interpretacion_camino by auto
              hence "(v,?u)\<in> r"
                using  `u\<in>A` `v\<in>A` `?u\<in>A` `(v,u)\<in> r` `trans_en A r`
                by(unfold trans_en_def, blast)
              hence "valor (interpretacion_camino A r ?u) (Atomo v) =  Verdad"
                by auto
              thus False using 2 by auto
            qed
          next
            assume  "F \<in> \<H>' A r"
            hence "\<exists>n. F \<in> \<H>n A r n" by(unfold  \<H>'_def, auto)
            then obtain n where  "F \<in> \<H>n A r n" by auto
            hence
            "\<exists>u. \<exists>v. F = \<not>.((Atomo u) \<and>. (Atomo v)) \<and> u\<in>(nivel A r n) \<and>
             v\<in>(nivel A r n) \<and> u\<noteq>v"
              by(unfold \<H>n_def, auto)
            then obtain u v where F: "F = \<not>.((Atomo u) \<and>. (Atomo v))"
            and "u\<in>(nivel A r n)" and "v\<in>(nivel A r n)" and "u\<noteq>v"
              by auto
            show "valor (interpretacion_camino A r ?u) F = Verdad"
            proof(rule ccontr)
              assume "valor (interpretacion_camino A r ?u) F \<noteq> Verdad"
              hence "valor (interpretacion_camino A r ?u) F = Falso"
                using CasosValor by auto
              hence
              "valor (interpretacion_camino A r ?u)((Atomo u) \<and>.
               (Atomo v)) = Verdad"
                using F  ValoresNegacion1 by blast
              hence "valor (interpretacion_camino A r ?u)(Atomo u) = Verdad \<and>
              valor (interpretacion_camino A r ?u)(Atomo v) = Verdad"
                using ValoresConjuncion by blast
              hence "(u,?u)\<in>r" and  "(v,?u)\<in>r"
                using  valor_interpretacion_camino by auto
              hence a: "(nivel A r n) \<inter> (nivel A r n) = {}"
                using `arbol A r`  `u\<in>(nivel A r n)`  `v\<in>(nivel A r n)`  `u\<noteq>v`
                niveles_diferentes_arbol1[of A r]
                by blast
              have "(nivel A r n) \<noteq> {}"
                using  `v\<in>(nivel A r n)` by auto
              thus False using a by auto
            qed
          qed
        qed
      qed
    qed
  qed
  thus "satisfacible S" by(unfold satisfacible_def, auto)
qed

definition \<B>:: "'a set \<Rightarrow> ('a  \<Rightarrow> v_verdad) \<Rightarrow> 'a set" where
"\<B> A I  \<equiv> {u|u. u\<in>A \<and> valor I (Atomo u) = Verdad}"

lemma valor_disyuncion_lista1:
  assumes "valor I (disyuncion_nodos (a # l)) = Verdad"
  shows "valor I (Atomo a) = Verdad \<or> valor I (disyuncion_nodos l) = Verdad"
proof-
  have "disyuncion_nodos (a # l) = (Atomo a) \<or>. (disyuncion_nodos l)"
    by auto
  hence "valor I ((Atomo a) \<or>. (disyuncion_nodos l)) = Verdad"
    using assms by auto
  thus ?thesis using ValoresDisyuncion by blast
qed

lemma valor_disyuncion_lista:
  assumes "valor I (disyuncion_nodos l) = Verdad"
  shows "\<exists>x. x \<in> set l \<and> valor I (Atomo x) = Verdad"
proof-
  have "valor I (disyuncion_nodos l) = Verdad \<Longrightarrow>
  \<exists>x. x \<in> set l \<and>  valor I (Atomo x) = Verdad"
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    show  "\<exists>x. x \<in> set (a # l) \<and> valor I (Atomo x) = Verdad"
    proof-
      have "valor I (Atomo a) = Verdad \<or> valor I (disyuncion_nodos l)=Verdad"
        using Cons(2) valor_disyuncion_lista1[of I] by auto
      thus ?thesis
    proof(rule disjE)
      assume "valor I (Atomo a) = Verdad"
      thus ?thesis by auto
    next
      assume "valor I (disyuncion_nodos l) = Verdad"
      thus ?thesis
        using Cons by auto
    qed
  qed
qed
  thus ?thesis using assms by auto
qed

lemma interseccion_rama_nivel1:
  assumes "arbol_infinito A r" and "ramificacion_finita A r"
  and I: "\<forall>F \<in> (\<F>' A r). valor I F = Verdad"
shows "\<forall>n. \<exists>x. x \<in> nivel A r n \<and> x \<in> (\<B> A I)" using niveles_no_vacios
proof-
  fix n
  have "\<forall>n. valor I (disyuncion_nodos(conj_a_lista (nivel A r n))) = Verdad"
    using I by (unfold \<F>'_def, auto)
  hence 1:
  "\<forall>n. \<exists>x. x \<in> set (conj_a_lista (nivel A r n)) \<and> valor I (Atomo x) = Verdad"
    using valor_disyuncion_lista by auto
  have "arbol A r"
    using `arbol_infinito A r`by auto
  hence "\<forall>n .set (conj_a_lista (nivel A r n)) = nivel A r n"
    using assms(1-2) lista_conjunto by auto
  hence  "\<forall>n. \<exists>x. x \<in> nivel A r n \<and>  valor I (Atomo x) = Verdad"
    using 1  by auto
  hence  "\<forall>n. \<exists>x. x \<in> nivel A r n \<and> x\<in>A \<and> valor I (Atomo x) = Verdad"
    by(unfold nivel_def, auto)
  thus ?thesis using \<B>_def[of A I] by auto
qed

lemma interseccion_rama_nivel2:
  assumes I:  "\<forall>F \<in> (\<H>' A r). valor I F = Verdad"
  and "x\<in>(\<B> A I)"  and  "y\<in>(\<B> A I)"  and  "x \<noteq> y" and  n: "x \<in> nivel A r n"
  and m: "y \<in> nivel A r m"
shows  "n \<noteq> m"
proof(rule ccontr)
  assume "\<not> n \<noteq> m"
  hence "n=m" by auto
  have "x\<in>A" and  "y\<in>A" and v1: "valor I (Atomo x) = Verdad"
  and v2: "valor I (Atomo y) = Verdad"
    using  `x\<in>(\<B> A I)` `y\<in>(\<B> A I)`  by(unfold \<B>_def, auto)
  have "\<not>.((Atomo x) \<and>. (Atomo y)) \<in> (\<H>n A r n)"
    using `x\<in>A`   `y\<in>A`  `x \<noteq> y` n m `n=m`
    by(unfold \<H>n_def, auto)
  hence "\<not>.((Atomo x) \<and>. (Atomo y)) \<in> (\<H>' A r)"
    by(unfold \<H>'_def, auto)
  hence "valor I (\<not>.((Atomo x) \<and>. (Atomo y))) = Verdad"
    using I by auto
  moreover
  have "valor I ((Atomo x) \<and>. (Atomo y)) = Verdad"
    using v1 v2 v_conjuncion_def by auto
  hence "valor I (\<not>.((Atomo x) \<and>. (Atomo y))) = Falso"
    using v_negacion_def by auto
  ultimately
  show False by auto
qed

lemma interseccion_rama_nivel:
  assumes  "arbol_infinito A r" and "ramificacion_finita A r"
  and I: "\<forall>F \<in> (\<F>' A r) \<union> (\<H>' A r). valor I F = Verdad"
shows "\<forall>n. \<exists>u. (\<B> A I) \<inter>  nivel A r n = {u}"
proof
  fix n
  show "\<exists>u. (\<B> A I) \<inter> nivel A r n = {u}"
  proof-
    have "\<exists>u. u \<in> nivel A r n \<and> u \<in> (\<B> A I)"
      using assms interseccion_rama_nivel1[of A r I] by auto
    then obtain u where u: "u \<in> nivel A r n \<and> u\<in>(\<B> A I)" by auto
    hence 1:  "{u} \<subseteq> (\<B> A I) \<inter> nivel A r n" by blast
    have 2:  "(\<B> A I) \<inter> nivel A r n \<subseteq> {u}"
    proof(rule subsetI)
      fix x
      assume  "x\<in>(\<B> A I) \<inter> nivel A r n"
      hence 2: "x\<in>(\<B> A I) \<and> x\<in> nivel A r n"  by auto
      have "u = x"
      proof(rule ccontr)
        assume "u \<noteq> x"
        hence "n\<noteq>n"
          using u 2 I interseccion_rama_nivel2[of A r] by blast
        thus False by auto
      qed
      thus "x\<in>{u}" by auto
    qed
    have "(\<B> A I) \<inter> nivel A r n = {u}"
      using 1 2 by auto
    thus "\<exists>u.(\<B> A I) \<inter>  nivel A r n = {u}"  by auto
  qed
qed

lemma predecesor_rama:
  assumes I:  "\<forall>F \<in> (\<G>' A r). valor I F = Verdad"
  and "y\<in>(\<B> A I)"  and  "(x,y)\<in> r" and "x\<in>A" and "y\<in>A"
shows "x\<in>(\<B> A I)"
proof-
  have "(Atomo y) \<rightarrow>. (Atomo x)\<in> \<G>' A r"
    using `x\<in>A`  `y\<in>A`  `(x, y)\<in>r` by (unfold  \<G>'_def, auto)
  hence "valor I ((Atomo y) \<rightarrow>. (Atomo x)) = Verdad"
    using I by auto
  moreover
  have "valor I (Atomo y) = Verdad"
    using  `y\<in>(\<B> A I)` by(unfold \<B>_def, auto)
  ultimately
  have "valor I (Atomo x) = Verdad"
    using v_implicacion_def by  auto
  thus  "x\<in>(\<B> A I)" using  `x\<in>A`  by(unfold \<B>_def, auto)
qed

lemma rama:
  assumes  "arbol_infinito A r" and "ramificacion_finita A r"
  and I: "\<forall>F \<in> (\<T>' A r). valor I F = Verdad"
shows "rama (\<B> A I) A r"
proof(unfold rama_def)
  let ?B = "(\<B> A I)"
  have "arbol A r"
  using  `arbol_infinito A r` by auto
  have "\<forall>F \<in> (\<F>' A r) \<union> (\<G>' A r) \<union> (\<H>' A r). valor I F = Verdad"
    using I by(unfold \<T>'_def)
  hence I1:  "\<forall>F \<in> (\<F>' A r). valor I F = Verdad"
  and   I2:  "\<forall>F \<in> (\<G>' A r). valor I F = Verdad"
  and   I3:  "\<forall>F \<in> (\<H>' A r). valor I F = Verdad"
    by auto
  have 0: "sub_orden_lineal_en ?B A r"
  proof(unfold sub_orden_lineal_en_def)
    have 1: "?B \<subseteq> A"  by(unfold \<B>_def, auto)
    have 2: "orden_parcial_estricto_en A r"
      using `arbol A r` arbol[of A r] by auto
    have "total_en ?B r"
    proof(unfold total_en_def)
      show "\<forall>x\<in>?B. \<forall>y\<in>?B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
      proof
        fix x
        assume "x\<in>?B"
        show "\<forall>y\<in>?B. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
        proof
          fix y
          assume "y\<in>?B"
          show "x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
          proof(rule impI)
            assume "x \<noteq> y"
            have "x\<in>A" and "y\<in>A" and v1: "valor I (Atomo x) = Verdad"
            and v2: "valor I (Atomo y) = Verdad"
              using `x\<in>?B` `y\<in>?B`  by(unfold \<B>_def, auto)
            have "(\<exists>n. x \<in> nivel A r n)" and "(\<exists>m. y \<in> nivel A r m)"
              using `x\<in>A` and `y\<in>A` nivel_elemento[of A r]
              by auto
            then obtain n m
            where n: "x \<in> nivel A r n" and m: "y \<in> nivel A r m"
              by auto
            have "n\<noteq>m"
              using I3 `x\<in>?B` `y\<in>?B` `x \<noteq> y` n m
                    interseccion_rama_nivel2[of A r]
              by auto
            hence "n<m \<or> m<n" by auto
            thus "(x, y) \<in> r \<or> (y, x) \<in> r"
            proof(rule disjE)
              assume  "n < m"
              have "(x, y) \<in> r"
              proof(rule ccontr)
                assume "(x, y) \<notin> r"
                have "\<exists>z. (z, y)\<in>r \<and> z \<in> nivel A r n"
                  using `arbol A r` `y \<in> nivel A r m` `n < m`
                         camino1[of A r y "m-1"]
                  by auto
                then obtain z where z1: "(z, y)\<in>r" and z2: "z \<in> nivel A r n"
                  by auto
                have "z\<in>A" using  `arbol A r` arbol z1 by auto
                hence "z\<in>(\<B> A I)"
                  using I2 `y\<in>A` `y\<in>?B` `(z, y)\<in>r` predecesor_rama[of A r I y z]
                  by auto
                have "x\<noteq>z" using `(x, y) \<notin> r` `(z, y)\<in>r` by auto
                hence "n\<noteq>n"
                  using I3 `x\<in>?B` `z\<in>?B` n z2  interseccion_rama_nivel2[of A r]
                  by blast
                thus False by auto
              qed
              thus "(x, y) \<in> r \<or> (y, x) \<in> r" by auto
            next
              assume "m < n"
              have "(y, x) \<in> r"
              proof(rule ccontr)
                assume "(y, x) \<notin> r"
                have "\<exists>z. (z, x)\<in>r \<and> z \<in> nivel A r m"
                  using `arbol A r`  `x \<in> nivel A r n`  `m < n`
                         camino1[of A r x "n-1"]
                  by auto
                  then obtain z where z1: "(z, x)\<in>r" and z2: "z \<in> nivel A r m"
                  by auto
                have "z\<in>A" using  `arbol A r` arbol z1 by auto
                hence  "z\<in>(\<B> A I)"
                  using I2 `x\<in>A` `x\<in>?B` `(z, x)\<in>r` predecesor_rama[of A r I x z]
                  by auto
                have "y\<noteq>z" using `(y, x) \<notin> r` `(z, x)\<in>r` by auto
                hence "m\<noteq>m"
                  using I3 `y\<in>?B` `z\<in>?B` m z2 interseccion_rama_nivel2[of A r ]
                  by blast
                thus False by auto
              qed
              thus "(x, y) \<in> r \<or> (y, x) \<in> r" by auto
            qed
          qed
        qed
      qed
    qed
    thus 3: "?B \<subseteq> A \<and> orden_parcial_estricto_en A r \<and> total_en ?B r"
      using 1 2 by auto
  qed
  have 4: "(\<forall>C. ?B \<subseteq> C \<and> sub_orden_lineal_en C A r \<longrightarrow> ?B = C)"
  proof
    fix C
    show "?B \<subseteq> C \<and> sub_orden_lineal_en C A r \<longrightarrow> ?B = C"
    proof(rule impI)
      assume "?B \<subseteq> C \<and> sub_orden_lineal_en C A r"
      hence "?B \<subseteq> C" and  "sub_orden_lineal_en C A r" by auto
      have "C \<subseteq> ?B"
      proof(rule subsetI)
          fix x
          assume "x\<in> C"
        have "C \<subseteq> A"
          using `sub_orden_lineal_en C A r`
         by(unfold sub_orden_lineal_en_def, auto)
        hence "x\<in>A" using `x\<in>C` by auto
        have "\<exists>n. x\<in>nivel A r n"
          using `x\<in>A` nivel_elemento[of A] by auto
        then obtain n where n: "x\<in>nivel A r n" by auto
        have "\<exists>u. (\<B> A I) \<inter> nivel A r n = {u}"
          using assms(1,2) I1 I3 interseccion_rama_nivel[of A r]
          by blast
        then obtain u where i: "(\<B> A I) \<inter> nivel A r n = {u}"
          by auto
        hence "u\<in>A" and u: "u \<in> nivel A r n"
         by(unfold nivel_def, auto)
        have "x=u"
        proof(rule ccontr)
          assume hip: "x\<noteq>u"
          have "u\<in>(\<B> A I)" using i by auto
          hence "u\<in>C" using `?B \<subseteq> C` by auto
          have "total_en C r"
            using `sub_orden_lineal_en C A r` sub_orden_lineal_en_def[of C A r]
            by blast
          hence "(x,u)\<in>r \<or> (u,x)\<in>r"
            using hip `x\<in>C` `u\<in>C` `sub_orden_lineal_en C A r`
            by(unfold total_en_def,auto)
          thus False
          proof(rule disjE)
            assume "(x,u)\<in>r"
            have "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r"
            and "finite (predecesores_de A u r)"
              using `u\<in>A` `arbol A r` arbol[of A r] by auto
            hence  "(nivel A r n) \<noteq> (nivel A r n)"
              using `(x,u)\<in>r` `x \<in> nivel A r n` `u \<in> nivel A r n`
                    pertenecen_niveles_diferentes[of r A ] by blast
            thus False by auto
          next
            assume "(u,x)\<in>r"
            have "r \<subseteq> A \<times> A" and "orden_parcial_estricto_en A r"
            and "finite (predecesores_de A x r)"
              using `x\<in>A` `arbol A r` arbol[of A r]  by auto
            hence "(nivel A r n) \<noteq> (nivel A r n)"
              using `(u,x)\<in>r` `u \<in> nivel A r n` `x \<in> nivel A r n`
                    pertenecen_niveles_diferentes[of r A ] by blast
            thus False by auto
          qed
        qed
        thus "x \<in> ?B" using i by auto
      qed
      thus  "?B = C"  using `?B \<subseteq> C` by blast
    qed
  qed
  thus "sub_orden_lineal_en (\<B> A I) A r \<and>
          (\<forall>C. \<B> A I \<subseteq> C \<and> sub_orden_lineal_en C A r \<longrightarrow> \<B> A I = C)"
    using `sub_orden_lineal_en (\<B> A I) A r` by auto
qed

lemma sobreyectiva_infinito:
  assumes  "\<exists>f:: 'a \<Rightarrow> nat. \<forall>n. \<exists>x\<in>A. n = f(x)"
  shows "infinite A"
proof(rule ccontr)
  assume "\<not> infinite A"
  hence "finite A" by auto
  hence "\<exists>n. \<exists>g. A = g ` {i::nat. i < n}"
    using finite_imp_nat_seg_image_inj_on[of A] by auto
  then obtain n g where g: "A = g ` {i::nat. i < n}" by auto
  obtain f where  "(\<forall>n. \<exists>x\<in>A. n = (f:: 'a \<Rightarrow>  nat)(x))"
    using assms by auto
  hence "\<forall>m. \<exists>k\<in>{i::nat. i < n}. m =(f \<circ> g)(k)"
    using g  by auto
  hence  "(UNIV :: nat set)  = (f \<circ> g) ` {i::nat. i < n}"
    by blast
  hence  "finite (UNIV :: nat set)"
    using nat_seg_image_imp_finite by blast
  thus False by auto
qed

lemma familia_interseccion_infinita:
  fixes P :: " nat \<Rightarrow> 'a set"
  assumes "\<forall>n. \<forall>m. n \<noteq> m \<longrightarrow> P n \<inter> P m = {}"
  and  "\<forall>n. (A \<inter> (P n)) \<noteq> {}"
  shows "infinite (\<Union>n. (A \<inter> (P n)))"
proof-
  let ?f = "\<lambda>x. SOME n. x\<in>(A \<inter> (P n))"
  have "\<forall>n. \<exists>x\<in>(\<Union>n. (A \<inter> (P n))). n = ?f(x)"
  proof
    fix n
    obtain a where a:  "a \<in> (A \<inter> (P n))" using assms(2) by auto
    {fix m
    have  "a \<in> (A \<inter> (P m)) \<longrightarrow> m=n"
    proof(rule impI)
      assume hip: "a \<in> A \<inter> P m" show "m =n"
      proof(rule ccontr)
        assume "m \<noteq> n"
        hence "P m \<inter> P n = {}" using assms(1) by auto
        thus False using a hip by auto
      qed
    qed}
    hence "\<And>m. a \<in> A \<inter> P m \<Longrightarrow> m = n" by auto
    hence 1: "?f(a) = n"  using a  some_equality by auto
    have "a\<in>(\<Union>n. (A \<inter> (P n)))" using a by auto
    thus "\<exists>x\<in>\<Union>n. A \<inter> P n. n = (SOME n. x \<in> A \<inter> P n)" using 1 by auto
  qed
  hence  "\<exists>f:: 'a \<Rightarrow>  nat. \<forall>n. \<exists>x\<in>((\<Union>n. (A \<inter> (P n)))). n = f(x)"
    using exI  by auto
  thus ?thesis using sobreyectiva_infinito by auto
qed

lemma rama_infinita:
  assumes  "arbol_infinito A r" and  "ramificacion_finita A r"
  and  I: "\<forall>F \<in> (\<F>' A r). valor I F = Verdad"
shows "infinite (\<B> A I)"
proof-
  have a: "\<forall>n. \<forall>m.  n \<noteq> m \<longrightarrow> nivel A r n \<inter> nivel A r m = {}"
    using niveles_distintosa[of _ _ A r] by auto
  have  "\<forall>n. \<B> A I \<inter> nivel A r n \<noteq> {}"
    using `arbol_infinito A r`
          `ramificacion_finita A r` I  interseccion_rama_nivel1[of A r]
    by blast
  hence  "infinite (\<Union>n. (\<B> A I) \<inter>  nivel A r n)"
    using familia_interseccion_infinita  a  by auto
  thus "infinite (\<B> A I)"by auto
qed

theorem Konig:
  assumes  "arbol_infinito (A::'nodos set) r"
  and  "enumeracion (g:: nat \<Rightarrow>'nodos)"
  and "ramificacion_finita A r"
  shows  "\<exists>B. rama_infinita B A r"
proof-
  have  "satisfacible (\<T>' A r)"
  proof-
    have "\<forall> S. S \<subseteq> (\<T>' A r) \<and> (finite S) \<longrightarrow> satisfacible S"
      using `arbol_infinito A r` `ramificacion_finita A r` camino_satisfacible
      by auto
    moreover
    have "\<exists>h. enumeracion (h:: nat \<Rightarrow>'nodos formula)"
      using EnumeracionFormulasP1[OF  `enumeracion (g:: nat \<Rightarrow>'nodos)`]
      by auto
    ultimately
    show "satisfacible (\<T>' A r)"
      using TeoremaCompacidad1[of "(\<T>' A r)"] by auto
  qed
  hence "\<exists>I. (\<forall>F \<in> (\<T>' A r). valor I F = Verdad)"
    by(unfold satisfacible_def, unfold modelo_def, auto)
  then obtain I where I:  "\<forall>F \<in> (\<T>' A r). valor I F = Verdad"
    by auto
  hence "\<forall>F \<in> (\<F>' A r) \<union> (\<G>' A r) \<union> (\<H>' A r). valor I F = Verdad"
    by(unfold \<T>'_def)
  hence I1:  "\<forall>F \<in> (\<F>' A r). valor I F = Verdad"
  and   I2:  "\<forall>F \<in> (\<G>' A r). valor I F = Verdad"
  and   I3:  "\<forall>F \<in> (\<H>' A r). valor I F = Verdad"
    by auto
  let ?B = "(\<B> A I)"
  have "rama_infinita ?B A r"
  proof(unfold rama_infinita_def)
    show "rama ?B A r \<and> infinite ?B"
    proof(rule conjI)
      show "rama ?B A r"
        using  `arbol_infinito A r` `ramificacion_finita A r` I rama[of A r]
        by auto
      show "infinite (\<B> A I)"
        using `arbol_infinito A r` `ramificacion_finita A r` I1 rama_infinita
      by auto
    qed
  qed
  thus "\<exists>B. rama_infinita B A r" by auto
qed

end
