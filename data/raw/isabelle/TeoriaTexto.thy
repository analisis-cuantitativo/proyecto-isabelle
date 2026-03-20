(*<*)
theory TeoriaTexto
imports Main
begin
(*>*)

text\<open>
%
\begin{isabellebody}%
\def\isabellecontext{T{\isadigit{1}}SintaxisSemanticaP}%
%
\isadelimtheory
%
\endisadelimtheory
%
\isatagtheory
%
\endisatagtheory
{\isafoldtheory}%
%
\isadelimtheory
%
\endisadelimtheory
%
\begin{isamarkuptext}%
\label{cap4}%
\end{isamarkuptext}%
\isamarkuptrue%
%
\isamarkupsection{Sintaxis y Semántica Proposicional%
}
\isamarkuptrue%
%
\begin{isamarkuptext}%
\label{sintaxsemanticaP}
  En la lógica objeto proposicional que consideramos, las fórmulas se cons-truyen a partir de las
  conectivas  \isa{{\isasymbottom}{\isacharcomma}\ {\isasymtop}{\isacharcomma}\ {\isasymnot}{\isacharcomma}\ {\isasymand}{\isacharcomma}\ {\isasymor}{\isacharcomma}\ {\isasymrightarrow}}.
La sintaxis y semántica de la l\'ogica proposicional y su formalizaci\'on es la siguiente.

  \begin{definicion}
    El \textbf{alfabeto} de un lenguaje proposicional se compone de los
    siguientes símbolos.
    \begin{enumerate}
      \item \textbf{Símbolos lógicos:}
        \begin{itemize}
          \item[] conectivas: \isa{{\isasymbottom}{\isacharcomma}\ {\isasymtop}{\isacharcomma}\ {\isasymnot}{\isacharcomma}\ {\isasymand}{\isacharcomma}\ {\isasymor}{\isacharcomma}\ {\isasymrightarrow}}
          \item[] símbolos de puntuación: '(' , ')'
        \end{itemize}
     \item \textbf{Símbolos no lógicos:}
         \begin{itemize}
           \item[] símbolos proposicionales $P_0, P_1, \dots$
         \end{itemize}
   \end{enumerate}
  \end{definicion}
  Las {\em fórmulas} se definen de la
  si\-guiente manera.
   \begin{definicion}
     El conjunto de {\bf{fórmulas}} es el conjunto más pequeño que
      satisface las si\-guientes condiciones:
         \begin{enumerate}
           \item Los símbolos $\bot$ y $\top$ son fórmulas.
           \item Cualquier símbolo proposicional es una fórmula.
           \item Si $F$ es una fórmula, entonces $\neg F$ es
                 una fórmula.
           \item Si $F$ y $G$ son fórmulas, entonces
                  $(F \wedge G), (F \vee G), (F \rightarrow G)$ son fórmulas.
        \end{enumerate}
  \end{definicion}

  El siguiente tipo de dato define en Isabelle las fórmulas de la
  lógica proposicional.%
\end{isamarkuptext}%

\begin{isabellebody}%
\isacommand{datatype}\isamarkupfalse%
\ {\isacharprime}b\ formula\ {\isacharequal}\ \isanewline
\ \ \ \ FF\isanewline
\ \ {\isacharbar}\ TT\isanewline
\ \ {\isacharbar}\ Atomo\ {\isacharprime}b\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \isanewline
\ \ {\isacharbar}\ Negacion\ \ \ \ \ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose}
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}{\isachardoublequoteopen}{\isasymnot}{\isachardot}{\isacharparenleft}{\isacharunderscore}{\isacharparenright}{\isachardoublequoteclose}\ {\isacharbrackleft}{\isadigit{1}}{\isadigit{1}}{\isadigit{0}}{\isacharbrackright}\ {\isadigit{1}}{\isadigit{1}}{\isadigit{0}}{\isacharparenright}\isanewline
\ \ {\isacharbar}\ Conjuncion\ \ {\isachardoublequoteopen}{\isacharprime}b\ formula\ \ \ \ \ {\isachardoublequoteclose}\ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose}
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}\isakeyword{infixl}\ {\isachardoublequoteopen}{\isasymand}{\isachardot}{\isachardoublequoteclose}\ \ {\isadigit{1}}{\isadigit{0}}{\isadigit{9}}{\isacharparenright}\isanewline
\ \ {\isacharbar}\ Disyuncion\ \ {\isachardoublequoteopen}{\isacharprime}b\ formula\ \ \ \ \ {\isachardoublequoteclose}\ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose} \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}\isakeyword{infixl}\ {\isachardoublequoteopen}{\isasymor}{\isachardot}{\isachardoublequoteclose}\ \ {\isadigit{1}}{\isadigit{0}}{\isadigit{8}}{\isacharparenright}\isanewline
\ \ {\isacharbar}\ Implicacion\ \ {\isachardoublequoteopen}{\isacharprime}b\ formula\ \ \ \ \ {\isachardoublequoteclose}\ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose} \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}\isakeyword{infixl}\ {\isachardoublequoteopen}{\isasymrightarrow}{\isachardot}{\isachardoublequoteclose}\ {\isadigit{1}}{\isadigit{0}}{\isadigit{0}}{\isacharparenright}%
\end{isabellebody}%


%
\begin{isamarkuptext}%
\par
En lo que sigue  presentamos la formalización de los conceptos
  semánticos de la lógica proposicional.  Para formalizar la noción
  de valor de una fórmula en una interpretación (\ref{valor}),
   introducimos los conceptos de valores de verdad
  (\ref{vverdad}) e interpretación (\ref{interpretacion}).
  \label{semanticap}

  \begin{definicion}\label{vverdad}
    Los \textbf{valores de verdad} de la lógica proposicional clásica
    son $\V$ (que se interpreta como \textbf{verdadero}) y $\F$ (que se
    interpreta como \textbf{falso}).
  \end{definicion}

  En la formalización se identifica el conjunto de los valores de verdad
  con el tipo \emph{v-verdad}, el valor $\V$ con la constante
  \emph{Verdad} y el valor $\F$ con la constante \emph{Falso}
  respectivamente.%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{datatype}\isamarkupfalse%
\ v{\isacharunderscore}verdad\ {\isacharequal}\ Verdad\ {\isacharbar}\ Falso%
\begin{isamarkuptext}%
\begin{definicion}\label{interpretacion}
    Una \textbf{interpretación} es una función del conjunto de los
    símbolos proposicionales en el conjunto de los valores de verdad.
  \end{definicion}
  La representación en Isabelle del concepto de interpretación es una
  función de la forma \isa{I\ \ {\isacharcolon}{\isacharcolon}\ {\isacharprime}b\ {\isasymRightarrow}\ \ v{\isacharunderscore}verdad}.

  Ahora  definimos por recursión el valor de una fórmula respecto de una
  interpretación.

\begin{definicion}\label{valor}
    El \textbf{valor} de una fórmula proposicional $F$ en una interpretación $I$
    (representado por $I'(F)$) se define por recursión como sigue:
    \begin{itemize}
    \item[] $I'(P) = I(P)$ si $P$ es un símbolo proposicional
    \item[] $I'(\neg F) = \begin{cases}
                         \V, & \text{si $I'(F) = \F$}\\
                         \F, & \text{si $I'(F) = \V$}
                        \end{cases}$
    \item[] $I'(F \wedge G)= \begin{cases}
                            \V, & \text{si $I'(F)=\V$ y $I'(G)=\V$}\\
                            \F, & \text{en caso contrario.}
                           \end{cases}$
    \item[] $I'(F \vee G)= \begin{cases}
                          \F, & \text{si $I'(F)=\F$ y $I'(G)=\F$}\\
                          \V, & \text{en caso contrario.}
                         \end{cases}$
     \item[] $I'(F \rightarrow G) = \begin{cases}
                                   \F, & \text{si $I'(F)=\V$ y $I'(G)=\F$}\\
                                   \V, & \text{en caso contrario.}
                                  \end{cases}$
    \end{itemize}
  \end{definicion}

  Para formalizarlo, definimos las funciones de verdad de las conectivas.%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}negacion\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}negacion\ x\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Verdad\ then\ Falso\ else\ Verdad{\isacharparenright}{\isachardoublequoteclose}\isanewline
\isanewline
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}conjuncion\ {\isacharcolon}{\isacharcolon}\ \ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}conjuncion\ x\ y\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Falso\ then\ Falso\ else\ y{\isacharparenright}{\isachardoublequoteclose}\isanewline
\isanewline
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}disyuncion\ {\isacharcolon}{\isacharcolon}\ \ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}disyuncion\ x\ y\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Verdad\ then\ Verdad\ else\ y{\isacharparenright}{\isachardoublequoteclose}\isanewline
\isanewline
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}implicacion\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}implicacion\ x\ y\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Falso\ then\ Verdad\ else\ y{\isacharparenright}{\isachardoublequoteclose}%
\begin{isamarkuptext}%
La formalización del valor de una fórmula es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{primrec}\isamarkupfalse%
\ valor\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}{\isacharprime}b\ {\isasymRightarrow}\ \ v{\isacharunderscore}verdad{\isacharparenright}\ {\isasymRightarrow}\ {\isacharprime}b\ formula\ \ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\isanewline
\isakeyword{where}\isanewline
\ \ \ {\isachardoublequoteopen}valor\ I\ FF\ {\isacharequal}\ Falso{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ TT\ {\isacharequal}\ Verdad{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}Atomo\ P{\isacharparenright}\ {\isacharequal}\ I\ P{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}{\isasymnot}{\isachardot}\ F{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}negacion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}F\ {\isasymand}{\isachardot}\ G{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}conjuncion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharparenleft}valor\ I\ G{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}F\ {\isasymor}{\isachardot}\ G{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}disyuncion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharparenleft}valor\ I\ G{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}F\ {\isasymrightarrow}{\isachardot}\ G{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}implicacion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharparenleft}valor\ I\ G{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}%

%
\begin{isamarkuptext}%
Formalizamos  las noción de satisfacibilidad en términos del concepto de \isa{mo-delo}.
  \begin{definicion}\label{modeloP}
    Una interpretación $I$ es \textbf{modelo} de un conjunto de fórmulas $S$
    si, para toda fórmula $F$ de $S$, $I'(F) = \V$.
  \end{definicion}

  \noindent Su formalización es:%
\end{isamarkuptext}%

\isamarkuptrue%
\isacommand{definition}\isanewline \isamarkupfalse%
\ modelo\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}{\isacharprime}b\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isacharparenright}\ {\isasymRightarrow}\ {\isacharprime}b\ formula\ set\ {\isasymRightarrow}\ bool\ \ \ \ \ \ {\isachardoublequoteclose}\ {\isacharparenleft}{\isachardoublequoteopen}{\isacharunderscore}\ modelo\ {\isacharunderscore}{\isachardoublequoteclose}\ {\isacharbrackleft}{\isadigit{8}}{\isadigit{0}}{\isacharcomma}{\isadigit{8}}{\isadigit{0}}{\isacharbrackright}\ {\isadigit{8}}{\isadigit{0}}{\isacharparenright}\isanewline \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}I\ modelo\ S\ {\isasymequiv}\ {\isacharparenleft}{\isasymforall}F\ {\isasymin}\ S{\isachardot}\ valor\ I\ F\ {\isacharequal}\ Verdad{\isacharparenright}{\isachardoublequoteclose}%

\begin{isamarkuptext}%
\begin{definicion}\label{satisfacibleP}
    Un conjunto de fórmulas es satisfacible si tiene algún mode\~ lo. En
    caso contrario se dice que es insatisfacible.
  \end{definicion}

  \noindent Su formalizacion es:%
\end{isamarkuptext}%

\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ satisfacible\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharprime}b\ formula\ set\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}satisfacible\ S\ {\isasymequiv}\ {\isacharparenleft}{\isasymexists}v{\isachardot}\ v\ modelo\ S{\isacharparenright}{\isachardoublequoteclose}%

\section{Teorema de Compacidad}

\begin{isamarkuptext}%
En esta sección presentamos las ideas principales de la manera como hemos formalizado el Teorema de Compacidad. En el anexo 1 se muestra el desa-rrollo completo de
la respectiva teoría.
\par
Para enunciar el Teorema de Compacidad necesitamos los conceptos de conjunto finito y conjunto enumerable.
\begin{definicion}
Sea $n$ un número natural. El segmento inicial deteminado por $n$ es el conjunto
$I_{n} = \{m\in \mathbb{N} \mid  m < n \}$.
\par \par
Un conjunto $A$ es finito si existe una función sobreyectiva $f\colon I_{n}\to A$ de algún segmento inicial $I_{n}$ en $A$. En caso contrario se dice que es infinito.
\end{definicion}

En Isabelle se define de manera inductiva el concepto de conjunto finito
\cite{DBLP:conf/tphol/NipkowP05}:%
\end{isamarkuptext}\isamarkuptrue%

\isacommand{inductive}\isamarkupfalse%
\ finite\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharprime}a\ set\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\isanewline
\ \ \isakeyword{where}\isanewline
\ \ \ \ emptyI{\isacharcolon}\ {\isachardoublequoteopen}\ \ \ \ finite\ {\isacharbraceleft}{\isacharbraceright}{\isachardoublequoteclose}\isanewline
\ \ {\isacharbar}\ insertI{\isacharcolon}\ {\isachardoublequoteopen}\ \ \ \ finite\ A\ {\isasymLongrightarrow}\ finite\ {\isacharparenleft}insert\ a\ A{\isacharparenright}{\isachardoublequoteclose}%
\begin{isamarkuptext}%
El siguiente lema afirma que las anteriores definiciones son equivalentes.%
\end{isamarkuptext}\isamarkuptrue%
\isacommand{lemma}\isamarkupfalse%
\ {\isachardoublequoteopen}finite\ A\ {\isasymlongleftrightarrow}\ {\isacharparenleft}{\isasymexists}n\ f{\isachardot}\ A\ {\isacharequal}\ f\ {\isacharbackquote}\ {\isacharbraceleft}i{\isacharcolon}{\isacharcolon}nat{\isachardot}\ i\ {\isacharless}\ n{\isacharbraceright}{\isacharparenright}{\isachardoublequoteclose}
%
\begin{isamarkuptext}%
\begin{definicion}
Un conjunto $A$ es enumerable si es vacío o existe una función sobreyectiva
 $f\colon \mathbb{N}\to A$ del conjunto de los números naturales en el conjunto $A$.
 En este caso, se dice que $f$ es una enumeración de $A$, y sus elementos se puede listar como una sucesión infinita:
$f(0),f(1),f(2), \ldots  $,
en la cual aparecen todos los elementos de $A$, con posibles repeticiones, y solo elementos de $A$.
En particular, cualquier conjunto finito es enumerable.
\end{definicion}
\end{isamarkuptext}
%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ enumeracion\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}nat\ {\isasymRightarrow}{\isacharprime}b{\isacharparenright}\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
 \ {\isachardoublequoteopen}enumeracion\ f\ {\isacharequal}\ {\isacharparenleft}{\isasymforall}y{\isachardot}{\isasymexists}n{\isachardot}\ y\ {\isacharequal}\ {\isacharparenleft}f\ n{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}%
%
\begin{isamarkuptext}%
\begin{teorema}[Teorema de Compacidad (3.6.3 en \cite{Fitting})]\label{compacidad}
  Sean $L$ un lenguaje proposicional enumerable y $S$ un
  conjunto de fórmulas proposicionales. Si todo subconjunto finito de
  $S$ es satisfacible, entonces $S$ es satisfacible.
\end{teorema}
\end{isamarkuptext}
%
\end{isabellebody}%
\<close>

text \<open>
  La demostración del Teorema de Compacidad que se presenta en los textos
  clásicos de introducción a la lógica utiliza el {\em Lema de
  König}. El Teorema de Existencia de Modelos  permite otra forma de
  demostrar este resultado.

 \begin{teorema}[Teorema de Existencia de Modelos (3.6.2 en \cite{Fitting})]\label{ConjuntosatisfacibleP}
  Sea $L$ un lenguaje proposicional enumerable. Si $\mathcal{C}$
  es una propiedad de consistencia proposicional y $S\in \mathcal{C}$,
  entonces $S$ es satisfacible.
  \end{teorema}
La formalizacion en Isabelle es la siguiente.
\newline
%
\begin{isabellebody}%
\isamarkuptrue%
\isacommand{theorem}\isamarkupfalse%
\ TeoremaExistenciaModelos{\isacharcolon}\isanewline
\ \ \isakeyword{assumes}\ h{\isadigit{1}}{\isacharcolon}\ {\isachardoublequoteopen}{\isasymexists}g{\isachardot}\ enumeracion\ {\isacharparenleft}g{\isacharcolon}{\isacharcolon}\ nat\ {\isasymRightarrow}\ {\isacharprime}b\ formula{\isacharparenright}{\isachardoublequoteclose}\ \ \isanewline
\ \ \isakeyword{and}\ h{\isadigit{2}}{\isacharcolon}\ {\isachardoublequoteopen}consistenciaP\ {\isasymC}{\isachardoublequoteclose}\ \isanewline
\ \ \isakeyword{and}\ h{\isadigit{3}}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}S{\isacharcolon}{\isacharcolon}\ {\isacharprime}b\ formula\ set{\isacharparenright}\ {\isasymin}\ {\isasymC}{\isachardoublequoteclose}\isanewline
\ \ \isakeyword{shows}\ {\isachardoublequoteopen}satisfacible\ S{\isachardoublequoteclose}\isanewline
%
\isadelimproof
%
\endisadelimproof
%
\end{isabellebody}

%

Para  aplicar el teorema anterior  en la formalización  del Teorema de Compacidad utilizamos
el siguiente lema.

  \begin{lema}\label{lemaComp}
  La colección de conjuntos de fórmulas proposicionales,
  $$\mathcal{C} =
   \{W|\forall A\, (A\subseteq W \wedge A\mbox{ es finito } \rightarrow
                   A\mbox{ es satisfacible})\}$$
  es una propiedad de consistencia.
  \end{lema}


\begin{isamarkuptext}%
La formalización del lema anterior es la siguiente.%
\end{isamarkuptext}\isamarkuptrue%
%
\begin{isabellebody}%
\isacommand{lemma}\isamarkupfalse%
\ ConsistenciaCompacidad{\isacharcolon}\ \ \ \isanewline
\ \ \isakeyword{shows}\ {\isachardoublequoteopen}consistenciaP{\isacharbraceleft}W{\isacharcolon}{\isacharcolon}{\isacharprime}b\ formula\ set{\isachardot}\ {\isasymforall}A{\isachardot}\ {\isacharparenleft}A{\isasymsubseteq}\ W\ {\isasymand}\ finite\ A{\isacharparenright}\ {\isasymlongrightarrow}\ \isanewline
\ \ satisfacible\ A{\isacharbraceright}{\isachardoublequoteclose}
%
\isadelimproof
%
\endisadelimproof
%
\begin{isamarkuptext}%
La formalización del Teorema de Compacidad es la siguiente:%
\end{isamarkuptext}\isamarkuptrue%
\isacommand{theorem}\isamarkupfalse%
\ TeoremaCompacidad{\isadigit{1}}{\isacharcolon}\isanewline
\ \ \isakeyword{assumes}\  {\isachardoublequoteopen}{\isasymexists}g{\isachardot}\ enumeracion\ {\isacharparenleft}g{\isacharcolon}{\isacharcolon}\ nat\ {\isasymRightarrow}\ {\isacharprime}b\ formula{\isacharparenright}{\isachardoublequoteclose}\ \ \isanewline
\ \ \isakeyword{and}\ {\isachardoublequoteopen}{\isasymforall}A{\isachardot}\ {\isacharparenleft}A\ {\isasymsubseteq}\ {\isacharparenleft}S{\isacharcolon}{\isacharcolon}\ {\isacharprime}b\ formula\ set{\isacharparenright}\ {\isasymand}\ finite\ A{\isacharparenright}\ {\isasymlongrightarrow}\ satisfacible\ A{\isachardoublequoteclose}\ \isanewline
\ \ \isakeyword{shows}\ {\isachardoublequoteopen}satisfacible\ S{\isachardoublequoteclose}\isanewline
%
\isadelimproof
%
\endisadelimproof




\end{isabellebody}%


\<close>






(*<*)
end
(*>*)
