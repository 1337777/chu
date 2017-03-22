(**#+TITLE: chuSolution.v

Proph

https://github.com/1337777/chu/blob/master/chuSolution.v

solves some question of 楚 [fn:1] which is how to program contextual limits of polymorph
functors.

This angle of view is that limits are described by some logical equalizers conditions onto some
computational products data, which is that the logical cone-condition onto the two computational
precone-morphisms data corresponds to the logical
containment-in-the-limit-subobject-of-the-product condition onto the one computational
pairing-morphism data.

Therefore oneself does not lack some very-complicated-induction scheme (beyond
induction-induction) on the whole limit. Instead oneself may primo erase/extract some logical
equalizers/cone-conditions by assuming some erasure/extraction scheme as axiom, then secondo
dissolve by reformulating the with-cuts cone-conditions on the two projections into some
cut-free cone-condition on the single projection, finally tertio resolve by cut-elimination into
some decidable only-congruence-style solution.

Moreover this decidability technique shall generalize to limits where the indexing graph is
finite or well-founded. Finally, memo that any total-limit (general Kan extension)
simply-axiomitize some bijection property of multiple-limits ("pointwise" Kan extension) :
(multiple copairings <=> one contextual multiple-cone) , whose equational formulation is similar
to the equational formulation for the common limits. Indeed this property says no-more-than some
commutation-of-polymorph-quantifiers bijection : (multiple contextual-cones <=> one contextual
multiple-cone). Therefore this decidability technique shall generalize to Kan extensions.

[fn:1] ~楚~ [[https://github.com/1337777/chu/blob/master/ocic03-what-is-normal.djvu]]

**)

(**

* Limits

#+BEGIN_SRC coq :exports both :results silent **)

Require Import borceuxSolution_half_old.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import Setoid.
Require Omega. 

Set Implicit Arguments.
Unset Strict Implicits.
Unset Printing Implicit Defensive.

(**#+END_SRC

** Equalizers

#+BEGIN_SRC coq :exports both :results silent **)

Import LOGIC.
Import LOGIC.Ex_Notations3.

Parameter perm : (* /!\ coherence, more arrows have same domain-codomain /!\ *)
  forall {log : logic} {V W : obV log}, log.-V(0 log.-(0 V & W )0 |- log.-(0 W & V )0 )0 .
Definition desIdenObLK :
  forall {log : logic} {V : obV log}, log.-V(0 log.-(0 log.-I & V )0 |- V )0
  := fun log V => Des (log.-uV) .
Parameter desIdenObLKV :
  forall {log : logic} {V : obV log}, log.-V(0 V |- log.-(0 log.-I & V )0 )0 .
Parameter desIdenObRK :
  forall {log : logic} {V : obV log}, log.-V(0 log.-(0 V & log.-I )0 |- V )0.
Parameter desIdenObRKV :
  forall {log : logic} {V : obV log}, log.-V(0 V |- log.-(0 V & log.-I )0 )0. 
Parameter desV01 : forall {log : logic} {V2 V2' V1 : obV log},
    log.-V(0 V2 |- V2' )0 -> log.-V(0 log.-(0 V1 & V2 )0 |- log.-(0 V1 & V2' )0 )0.
Notation  "dat .-(0 V1 & v )1" := (@desV01 dat _ _ V1 v)
                                    (at level 30, format "dat .-(0  V1  &  v  )1").
Notation  "(0 V1 & v )1" := (_ .-(0 V1 & v )1)
                              (at level 30, format "(0  V1  &  v  )1").

Parameter log : logic.

(* alternatively : no elim, Parameters,,, *)
Inductive obIndexer : Type :=
| IndexDom : obIndexer
| IndexCodom : obIndexer.

Reserved Notation "''Indexer' (0 V |- [0 A1 ~> A2 ]0 )0"
         (at level 25, format "''Indexer' (0  V  |-  [0  A1  ~>  A2  ]0 )0").

Parameter IndexerMultiplicity : obV log.

Inductive Indexer : obV log -> obIndexer -> obIndexer -> Type :=
  
| PolyV_Indexer : forall (V V' : obV log),
    V(0 V' |- V )0 -> forall (A1 A2 : obIndexer), 'Indexer(0 V |- [0 A1 ~> A2 ]0 )0 ->
                                           'Indexer(0 V' |- [0 A1 ~> A2 ]0 )0
| ReindexZeros :
    forall V', V(0 V' |- IndexerMultiplicity )0 ->
          'Indexer(0 V' |- [0 IndexDom ~> IndexCodom ]0 )0
                  
| ReindexData :
    forall V', V(0 V' |- IndexerMultiplicity )0 ->
          'Indexer(0 V' |- [0 IndexDom ~> IndexCodom ]0 )0

where "''Indexer' (0 V |- [0 A1 ~> A2 ]0 )0" := (@Indexer V A1 A2) . 

Parameter context0 : obIndexer -> obV log.
Parameter context1 : forall {V A A'}, 'Indexer(0 V |- [0 A ~> A' ]0 )0 ->
                                 V(0 (context0 A') |- (0 V & (context0 A) )0  )0.

Module LIMIT.

  Delimit Scope lim_scope with lim.
  Open Scope lim_scope.

  Parameter obCoMod : Type.
  Parameter CoMod00 : obV log -> obCoMod -> obCoMod -> Type.
  Notation "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0"
    := (@CoMod00 V A1 A2) (at level 25, format "''CoMod' (0  V  |-  [0  A1  ~>  A2  ]0 )0") : lim_scope.
  Parameter convCoMod : forall (V : obV log) (A1 A2 : obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> forall (A1'0 A2'0 : obCoMod), 'CoMod(0 V |- [0 A1'0 ~> A2'0 ]0 )0 -> Prop.
  Notation "f2 ~~~ f1" := (@convCoMod _ _ _ f2 _ _ f1) (at level 70) : lim_scope.

  Parameter Lim0 :
    forall (func0 : obIndexer -> obCoMod)
      (* alternatively: func0 as sequence, here have function extensionality because obIndexer is finite,,, *)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
      obCoMod.

  Parameter PolyV_CoMod : forall (V V' : obV log),
      V(0 V' |- V )0 -> forall (A1 A2 : obCoMod), 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 ->
                                         'CoMod(0 V' |- [0 A1 ~> A2 ]0 )0.

  Parameter UnitCoMod : forall (V : obV log), forall {A : obCoMod}
      ,  V(0 V |- log.-I )0 -> 'CoMod(0 V |- [0 A ~> A ]0 )0.

  Parameter PolyCoMod : forall (V : obV log) (A2 : obCoMod) (A1 : obCoMod)
    , 'CoMod(0 V |- [0 A2 ~> A1 ]0 )0 -> forall A1' : obCoMod, forall (W WV : obV log),
          V(0 WV |- (0 W & V )0 )0 ->
          'CoMod(0 W |- [0 A1 ~> A1' ]0 )0 -> 'CoMod(0 WV |- [0 A2 ~> A1' ]0 )0.

  Definition PolyV_CoMod_rewrite V V' A1 A2 v a :=
    (@PolyV_CoMod V V' v A1 A2 a).
  Notation "v o>' a" := (@PolyV_CoMod_rewrite _ _ _ _ v a)
                          (at level 25, right associativity, format "v  o>'  a") : lim_scope.
  Notation "v o>| 'uCoMod'" := (@UnitCoMod _ _ v)(at level 25) : lim_scope.
  Notation "v o>| @ 'uCoMod' A" :=
    (@UnitCoMod _ A v) (at level 25, only parsing) : lim_scope.
  Definition PolyCoMod_rewrite V A2 A1 A1' W WV wv a_ a' :=
    (@PolyCoMod V A2 A1 a_ A1' W WV wv a').
  Notation "v o>| a_ o>CoMod a'" :=
    (@PolyCoMod_rewrite _ _ _ _ _ _ v a_ a')
      (at level 25, right associativity, a_ at next level, format "v  o>|  a_  o>CoMod  a'") : lim_scope.
  
  Notation cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom :=
    ( ( ( ((0 _ & context1 (ReindexZeros (log.-1)) )1 o> Assoc o> (1 perm & _ )0 o> Assoc_Rev) o>| f_IndexDom o>CoMod func1_ReindexZeros )
          ~~~ f_IndexCodom )
    /\  ( ( ((0 _ & context1 (ReindexData (log.-1)) )1 o> Assoc o> (1 perm & _ )0 o> Assoc_Rev) o>| f_IndexDom o>CoMod func1_ReindexData )
        ~~~ f_IndexCodom )).

  Parameter Limitator :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
      (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
      cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom ->
      forall U', V(0 U' |- U )0 -> 'CoMod(0 U' |- [0 L ~> Lim0 func1_ReindexZeros func1_ReindexData ]0)0.

  Parameter Project_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B, 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0 -> forall UC, V(0 UC |- (0 U & context0 IndexDom )0 )0 ->
                                                           'CoMod(0 UC |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0 )0.

  Parameter Project_Codom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B, 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0 -> forall UC, V(0 UC |- (0 U & context0 IndexCodom )0 )0 ->
                                                           'CoMod(0 UC |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0 )0.


  Notation "u o>| << f_IndexDom , f_IndexCodom @ f_cone >>" :=
    (@Limitator _ _ _ _ _ f_IndexDom f_IndexCodom f_cone _ u) (at level 0) : lim_scope.
  Notation "u o>| << f_IndexDom , f_IndexCodom >>" :=
    (@Limitator _ _ _ _ _ f_IndexDom f_IndexCodom _ _ u) (at level 0) : lim_scope.

  Notation "uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b" :=
    (@Project_Dom _ func1_ReindexZeros func1_ReindexData _ _ b _ uc) (at level 25) : lim_scope.
  Notation "uc o>| ~_IndexDom o>CoMod b" :=
    (@Project_Dom _ _ _ _ _ b _ uc) (at level 25) : lim_scope.

  Notation "uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b" :=
    (@Project_Codom _ func1_ReindexZeros func1_ReindexData _ _ b _ uc) (at level 25) : lim_scope.
  Notation "uc o>| ~_IndexCodom o>CoMod b" :=
    (@Project_Codom _ _ _ _ _ b _ uc) (at level 25) : lim_scope.
  
  Parameter CoMod_ReflV : forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      a ~~~ a.

  Parameter CoMod_TransV : forall (V : obV log) (A1 A2 : obCoMod)
               (uTrans a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      uTrans ~~~ a -> forall (a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        a' ~~~ uTrans -> a' ~~~ a.

  Parameter CoMod_SymV : forall (V : obV log) (A1 A2 : obCoMod) (a a' : 'CoMod(0 V |- [0 A1 ~> A2]0 )0),
      a ~~~ a' -> a' ~~~ a.

  Parameter PolyV_CoMod_cong : forall (A1 A2 : obCoMod) (V V' : obV log) (v v' : V(0 V' |- V )0)
                                 (a a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      v' ~~ v -> a' ~~~ a -> ( v' o>' a' ) ~~~ ( v o>' a ).

  Parameter UnitCoMod_cong : forall (V : obV log), forall {A : obCoMod} (v v' : V(0 V |- log.-I )0),
        v' ~~ v -> v' o>| @uCoMod A ~~~ v o>| @uCoMod A.

  Parameter CoMod_cong :
      forall (V : obV log) (A A' : obCoMod) (a_ a_0 : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obCoMod) (a' a'0 : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
        v' ~~ v -> a_0 ~~~ a_ -> a'0 ~~~ a' -> ( v' o>| a_0 o>CoMod a'0 ) ~~~ ( v o>| a_ o>CoMod a' ).

  Parameter Limitator_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
      (f_IndexCodom f'_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall (f_cone : cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom)
      (f'_cone : cone func1'_ReindexZeros func1'_ReindexData f'_IndexDom f'_IndexCodom),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom ~~~ f_IndexDom) -> (f'_IndexCodom ~~~ f_IndexCodom) ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( u0 o>| << f'_IndexDom , f'_IndexCodom @ f'_cone >> ) ~~~ ( u o>| << f_IndexDom , f_IndexCodom @ f_cone >> ).

 Parameter Project_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc -> b0 ~~~ b ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexDom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b0)
        ~~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b ).

 Parameter Project_Codom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      uc0 ~~ uc -> b0 ~~~ b ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexCodom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b0 ) ~~~ ( uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b ).

 Parameter PolyV_CoMod_arrowLog :
      forall (V'' V' : obV log) (v' : V(0 V'' |- V' )0) (V : obV log)
        (v : V(0 V' |- V )0) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v' o> v ) o>' a )
          ~~~ ( v' o>' ( v o>' a )
                : 'CoMod(0 V'' |- [0 A1 ~> A2 ]0)0 ).

 Parameter UnitCoMod_arrowLog : forall (V V' : obV log) (A : obCoMod) (v : V(0 V |- log.-I )0)
                                   (v' : V(0 V' |- V )0),
      ( ( v' o> v ) o>| @uCoMod A )
        ~~~ (v' o>' (v o>| @uCoMod A)
             : 'CoMod(0 V' |- [0 A ~> A ]0)0 ).

 Parameter CoMod_arrowLog :
      forall (V : obV log) (A0 : obCoMod) (A : obCoMod)
        (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
      forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
        ( ( v0 o> v ) o>| a_ o>CoMod a' )
          ~~~ ( v0 o>' ( v o>| a_ o>CoMod a' )
                : 'CoMod(0 WV0 |- [0 A0 ~> A' ]0)0 ).

 Parameter CoMod_arrowPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0) (A0 : obCoMod) (A : obCoMod)
        (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( v0 o> log.-(0 _ & v )1 ) o>| a_ o>CoMod a' )
          ~~~ ( v0 o>| ( v o>' a_ ) o>CoMod a'
                : 'CoMod(0 WV' |- [0 A0 ~> A' ]0)0 ).

 Parameter CoMod_arrowPost :
      forall (V : obV log) (A0 : obCoMod) (A : obCoMod) (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obCoMod)
        (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
        ( ( w0 o> log.-(1 w & _ )0 ) o>| a_ o>CoMod a' )
          ~~~ ( w0 o>| a_ o>CoMod ( w o>' a' )
                : 'CoMod(0 W'V |- [0 A0 ~> A' ]0)0 ).

 Parameter Limitator_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
      (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall (f_cone : cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom),
    forall U' (u : V(0 U' |- U )0) U'' (u' : V(0 U'' |- U' )0),
        ((u' o> u) o>| << f_IndexDom , f_IndexCodom @ f_cone >>)
          ~~~ ( u' o>' (u o>| << f_IndexDom , f_IndexCodom @ f_cone >>)
                : 'CoMod(0 U'' |- [0 L ~> Lim0 func1_ReindexZeros func1_ReindexData ]0)0 ).

 Parameter Project_Dom_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
        forall UC UC' (uc' : V(0 UC' |- UC )0) (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
          ((uc' o> uc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            ~~~ ( uc' o>' (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC' |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0 )0 ).

 Parameter Project_Codom_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
        forall UC UC' (uc' : V(0 UC' |- UC )0) (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
          ((uc' o> uc) o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            ~~~ ( uc' o>' (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC' |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0 )0 ).

 Parameter Project_Dom_arrow :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U U' (u : V(0 U' |- U )0) B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
        forall UC (uc : V(0 UC |- (0 U' & context0 IndexDom )0 )0),
          ((uc o> log.-(1 u & _ )0) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            ~~~ (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>' b)
                 : 'CoMod(0 UC |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0 )0).

 Parameter Project_Codom_arrow :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U U' (u : V(0 U' |- U )0) B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
        forall UC (uc : V(0 UC |- (0 U' & context0 IndexCodom )0 )0),
          ((uc o> log.-(1 u & _ )0) o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            ~~~ (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>' b)
                 : 'CoMod(0 UC |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0 )0).

 Parameter PolyV_CoMod_unit :
      forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( a ) ~~~ ( log.-1 o>' a
                    : 'CoMod(0 V |- [0 A1 ~> A2 ]0)0 ).

 Parameter CoMod_unit :
      forall (A : obCoMod) (V : obV log) (v : V(0 V |- log.-I )0)
        (W : obV log) (A' : obCoMod) (a : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
        ( ( v0 o> log.-(0 W & v )1 o> desIdenObRK ) o>' a )
          ~~~ ( v0 o>| ( v o>| uCoMod ) o>CoMod a
                : 'CoMod(0 WV |- [0 A ~> A' ]0)0 ).

 Parameter CoMod_inputUnitCoMod :
      forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (w : V(0 W |- log.-I )0),
      forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
        ( ( w0 o> log.-(1 w & V )0 o> desIdenObLK ) o>' b )
          ~~~  ( w0 o>| b o>CoMod ( w o>| uCoMod )
                 : 'CoMod(0 WV |- [0 B ~> A ]0)0 ).

  (* non for reduction *)
 Parameter CoMod_morphism :
      forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0)
        (W_ : obV log) (A' : obCoMod) (a_ : 'CoMod(0 W_ |- [0 A ~> A' ]0 )0)
        (W' : obV log) (A'' : obCoMod) (a' : 'CoMod(0 W' |- [0 A' ~> A'' ]0 )0),
      forall (W_V : obV log) (v : V(0 W_V |- (0 W_ & V )0 )0),
      forall (W'W_V : obV log) (v0 : V(0 W'W_V |- (0 W' & W_V )0 )0),
        ( ( v0 o> (0 W' & v )1 o> Assoc ) o>| b o>CoMod ( log.-1 o>| a_ o>CoMod a' ) )
          ~~~ ( v0 o>| ( v o>| b o>CoMod a_ ) o>CoMod a'
                : 'CoMod(0 W'W_V |- [0 B ~> A'' ]0)0 ).

 Parameter Limitator_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
      (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall (f_cone : cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom),
    forall U' (u : V(0 U' |- U )0),
    forall T L' (l : 'CoMod(0 T |- [0 L' ~> L ]0 )0),
    forall U'T (u't : V(0 U'T |- (0 U' & T )0 )0),
      let l_o_f_IndexDom := ((Assoc_Rev o> (0 _ & perm )1 o> Assoc) o>| l o>CoMod f_IndexDom) in
      let l_o_f_IndexCodom := ((Assoc_Rev o> (0 _ & perm )1 o> Assoc) o>| l o>CoMod f_IndexCodom) in
      forall (l_o_f_cone : cone func1_ReindexZeros func1_ReindexData l_o_f_IndexDom l_o_f_IndexCodom),
        ((u't o> (1 u & _ )0) o>| << l_o_f_IndexDom , l_o_f_IndexCodom @ l_o_f_cone >>)
          ~~~ (u't o>| l o>CoMod (u o>| << f_IndexDom , f_IndexCodom @ f_cone >>)
               : 'CoMod(0 U'T |- [0 L' ~> Lim0 func1_ReindexZeros func1_ReindexData ]0)0).

 Parameter Project_Dom_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall U' B' (b' : 'CoMod(0 U' |- [0 B ~> B' ]0 )0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
    forall U'UC (u'uc : V(0 U'UC |- (0 U' & UC )0 )0),
      ( (u'uc o> (0 U' & uc )1 o> Assoc)
         o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod ((log.-1) o>| b o>CoMod b')  )
        ~~~ ( u'uc o>| (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) o>CoMod b' ).

 Parameter Project_Codom_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
    forall U' B' (b' : 'CoMod(0 U' |- [0 B ~> B' ]0 )0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
    forall U'UC (u'uc : V(0 U'UC |- (0 U' & UC )0 )0),
      ((u'uc o> (0 U' & uc )1 o> Assoc)
         o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod ((log.-1) o>| b o>CoMod b') )
        ~~~ ( u'uc o>| (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) o>CoMod b' ).

 Parameter Project_cone_ReindexZeros :
      forall (func0 : obIndexer -> obCoMod)
        (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0)0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      ( (uc o> (0 _ & context1 (ReindexZeros (log.-1)) )1 o> Assoc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (log.-1 o>| func1_ReindexZeros o>CoMod b) )
        ~~~ ( (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
              : 'CoMod(0 UC |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0)0 ).

 Parameter Project_cone_ReindexData :
      forall (func0 : obIndexer -> obCoMod)
        (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0)0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      ( (uc o> (0 _ & context1 (ReindexData (log.-1)) )1 o> Assoc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (log.-1 o>| func1_ReindexData o>CoMod b) )
        ~~~ ( (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
              : 'CoMod(0 UC |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0)0 ).

 (*  may or may not be reduced , and  for sense only , has alternative formulation for intermediate solution and final solution *)  
 Parameter Limitator_Project :
    forall (func0 : obIndexer -> obCoMod) (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U (u : V(0 U |- log.-I )0),
      let Project_IndexDom_Id := ((log.-1) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexDom))) in
      let Project_IndexCodom_Id := ((log.-1) o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexCodom))) in
    forall (Project_cone : cone func1_ReindexZeros func1_ReindexData Project_IndexDom_Id Project_IndexCodom_Id),
      forall U' (u' : V(0 U' |- U )0),
        ( (u' o> u) o>| @ uCoMod (Lim0 func1_ReindexZeros func1_ReindexData) )
          ~~~ ( u' o>| << Project_IndexDom_Id , Project_IndexCodom_Id @ Project_cone >>
                : 'CoMod(0 U' |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> Lim0 func1_ReindexZeros func1_ReindexData ]0)0 ).

 Parameter Project_Dom_Limitator :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
    (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall (f_cone : cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom),
    forall U' (u : V(0 U' |- U )0),
    forall UB B (b : 'CoMod(0 UB |- [0 func0 IndexDom ~> B ]0 )0),
    forall UBC (u'c : V(0 UBC |- (0 UB & context0 IndexDom )0 )0),
    forall UBCU' (u'cu : V(0 UBCU' |- (0 UBC & U' )0)0),
      ( (u'cu o> (0 _ & u )1 o> (1 u'c & _ )0 o> Assoc_Rev o> (0 _ & perm )1) o>| f_IndexDom o>CoMod b )
        ~~~ ( u'cu o>| (u o>| << f_IndexDom , f_IndexCodom @ f_cone >>) o>CoMod ( (u'c o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) : 'CoMod(0 _ |- [0 Lim0 func1_ReindexZeros func1_ReindexData ~> B ]0)0 )
              : 'CoMod(0 UBCU' |- [0 L ~> B ]0)0 ).

 Parameter Project_Codom_Limitator :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
    (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall (f_cone : cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom),
    forall U' (u : V(0 U' |- U )0),
    forall UB B (b : 'CoMod(0 UB |- [0 func0 IndexCodom ~> B ]0 )0),
    forall UBC (u'c : V(0 UBC |- (0 UB & context0 IndexCodom )0 )0),
    forall UBCU' (u'cu : V(0 UBCU' |- (0 UBC & U' )0)0),
      ( (u'cu o> (0 _ & u )1 o> (1 u'c & _ )0 o> Assoc_Rev o> (0 _ & perm )1) o>| f_IndexCodom o>CoMod b )
        ~~~ ( u'cu o>| (u o>| << f_IndexDom , f_IndexCodom @ f_cone >>) o>CoMod (u'c o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) ).


 Module ERASED.

 Inductive obCoMod : Type :=
   Lim0 : forall (func0 : obIndexer -> obCoMod), obCoMod.

 Delimit Scope erased_scope with erased.
 Open Scope erased.
 
 Reserved Notation "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0" (at level 25, format "''CoMod' (0  V  |-  [0  A1  ~>  A2  ]0 )0").

 Inductive CoMod00 : obV log -> obCoMod -> obCoMod -> Type :=
 | PolyV_CoMod : forall (V V' : obV log),
     V(0 V' |- V )0 -> forall (A1 A2 : obCoMod), 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 ->
                                          'CoMod(0 V' |- [0 A1 ~> A2 ]0 )0
 | UnitCoMod : forall (V : obV log), forall {A : obCoMod}
     ,  V(0 V |- log.-I )0 -> 'CoMod(0 V |- [0 A ~> A ]0 )0
 | PolyCoMod : forall (V : obV log) (A2 : obCoMod) (A1 : obCoMod)
   , 'CoMod(0 V |- [0 A2 ~> A1 ]0 )0 -> forall A1' : obCoMod, forall (W WV : obV log),
         V(0 WV |- (0 W & V )0 )0 ->
         'CoMod(0 W |- [0 A1 ~> A1' ]0 )0 -> 'CoMod(0 WV |- [0 A2 ~> A1' ]0 )0
 | Limitator :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U', V(0 U' |- U )0 -> 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 

 | Limitator_Dom :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
     forall U', V(0 U' |- U )0 -> 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 

 | Project_Dom :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B, 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0 -> forall UC, V(0 UC |- (0 U & context0 IndexDom )0 )0 ->
                                                              'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0

 | Project_Codom :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B, 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0 -> forall UC, V(0 UC |- (0 U & context0 IndexCodom )0 )0 ->
                                                                'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0

 where "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0" := (@CoMod00 V A1 A2) : erased_scope.

 Definition PolyV_CoMod_rewrite V V' A1 A2 v a :=
   (@PolyV_CoMod V V' v A1 A2 a).
 Notation "v o>' a" := (@PolyV_CoMod_rewrite _ _ _ _ v a)
                         (at level 25, right associativity, format "v  o>'  a") : erased_scope.
 Notation "v o>| 'uCoMod'" := (@UnitCoMod _ _ v)(at level 25) : erased_scope.
 Notation "v o>| @ 'uCoMod' A" :=
   (@UnitCoMod _ A v) (at level 25, only parsing) : erased_scope.
 Definition PolyCoMod_rewrite V A2 A1 A1' W WV wv a_ a' :=
   (@PolyCoMod V A2 A1 a_ A1' W WV wv a').
 Notation "v o>| a_ o>CoMod a'" :=
   (@PolyCoMod_rewrite _ _ _ _ _ _ v a_ a')
     (at level 25, right associativity, a_ at next level, format "v  o>|  a_  o>CoMod  a'") : erased_scope.

 Notation "u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>" :=
   (@Limitator _ func1_ReindexZeros func1_ReindexData _ _ f_IndexDom f_IndexCodom _ u) (at level 0) : erased_scope.
 Notation "u o>| << f_IndexDom , f_IndexCodom >>" :=
   (@Limitator _ _ _ _ _ f_IndexDom f_IndexCodom _ u) (at level 0) : erased_scope.

 Notation "u o>| << f_IndexDom  @ func1_ReindexZeros , func1_ReindexData >>" :=
   (@Limitator_Dom _ func1_ReindexZeros func1_ReindexData _ _ f_IndexDom _ u) (at level 0) : erased_scope.
 Notation "u o>| << f_IndexDom >>" :=
   (@Limitator_Dom _ _ _ _ _ f_IndexDom _ u) (at level 0) : erased_scope.

 Notation "uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b" :=
   (@Project_Dom _ func1_ReindexZeros func1_ReindexData _ _ b _ uc) (at level 25) : erased_scope.
 Notation "uc o>| ~_IndexDom o>CoMod b" :=
   (@Project_Dom _ _ _ _ _ b _ uc) (at level 25) : erased_scope.

 Notation "uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b" :=
   (@Project_Codom _ func1_ReindexZeros func1_ReindexData _ _ b _ uc) (at level 25) : erased_scope.
 Notation "uc o>| ~_IndexCodom o>CoMod b" :=
   (@Project_Codom _ _ _ _ _ b _ uc) (at level 25) : erased_scope.

 Reserved Notation "f2 ~~~ f1"  (at level 70).
 
 Inductive convCoMod : forall (V : obV log) (A1 A2 : obCoMod),
     'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=
   
 | CoMod_ReflV : forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
     a ~~~ a
       
 | CoMod_TransV : forall (V : obV log) (A1 A2 : obCoMod)
                    (uTrans a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
     uTrans ~~~ a -> forall (a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
       a' ~~~ uTrans -> a' ~~~ a
                          
 | CoMod_SymV : forall (V : obV log) (A1 A2 : obCoMod) (a a' : 'CoMod(0 V |- [0 A1 ~> A2]0 )0),
     a ~~~ a' -> a' ~~~ a

 | PolyV_CoMod_cong : forall (A1 A2 : obCoMod) (V V' : obV log) (v v' : V(0 V' |- V )0)
                        (a a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
     v' ~~ v -> a' ~~~ a -> ( v' o>' a' ) ~~~ ( v o>' a )
                                        
 | UnitCoMod_cong : forall (V : obV log), forall {A : obCoMod} (v v' : V(0 V |- log.-I )0),
       v' ~~ v -> v' o>| @uCoMod A ~~~ v o>| @uCoMod A

 | CoMod_cong :
     forall (V : obV log) (A A' : obCoMod) (a_ a_0 : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
     forall (W : obV log) (A'' : obCoMod) (a' a'0 : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
     forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
       v' ~~ v -> a_0 ~~~ a_ -> a'0 ~~~ a' -> ( v' o>| a_0 o>CoMod a'0 ) ~~~ ( v o>| a_ o>CoMod a' )

 | Limitator_cong :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom f'_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u u0 : V(0 U' |- U )0),
       u0 ~~ u -> (f'_IndexDom ~~~ f_IndexDom) -> (f'_IndexCodom ~~~ f_IndexCodom) ->
       (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
       (func1'_ReindexData ~~~ func1_ReindexData) ->
       ( u0 o>| << f'_IndexDom , f'_IndexCodom @ func1'_ReindexZeros , func1'_ReindexData >> ) ~~~ ( u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >> )

 | Limitator_Dom_cong :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom ~~~ f_IndexDom) ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( u0 o>| << f'_IndexDom @ func1'_ReindexZeros , func1'_ReindexData >> ) ~~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

 | Project_Dom_cong :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
     forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
       uc0 ~~ uc -> b0 ~~~ b ->
       (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
       (func1'_ReindexData ~~~ func1_ReindexData) ->
       ( uc0 o>| ~_IndexDom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b0) ~~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

 | Project_Codom_cong :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
     forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
       uc0 ~~ uc -> b0 ~~~ b ->
       (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
       (func1'_ReindexData ~~~ func1_ReindexData) ->
       ( uc0 o>| ~_IndexCodom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b0 ) ~~~ ( uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

 | PolyV_CoMod_arrowLog :
     forall (V'' V' : obV log) (v' : V(0 V'' |- V' )0) (V : obV log)
       (v : V(0 V' |- V )0) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
       ( ( v' o> v ) o>' a )
         ~~~ ( v' o>' ( v o>' a )
               : 'CoMod(0 V'' |- [0 A1 ~> A2 ]0)0 )

 | UnitCoMod_arrowLog : forall (V V' : obV log) (A : obCoMod) (v : V(0 V |- log.-I )0)
                          (v' : V(0 V' |- V )0),
     ( ( v' o> v ) o>| @uCoMod A )
       ~~~ (v' o>' (v o>| @uCoMod A)
            : 'CoMod(0 V' |- [0 A ~> A ]0)0 )

 | CoMod_arrowLog :
     forall (V : obV log) (A0 : obCoMod) (A : obCoMod)
       (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
     forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
     forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
     forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
       ( ( v0 o> v ) o>| a_ o>CoMod a' )
         ~~~ ( v0 o>' ( v o>| a_ o>CoMod a' )
               : 'CoMod(0 WV0 |- [0 A0 ~> A' ]0)0 )

 | CoMod_arrowPre :
     forall (V V' : obV log) (v : V(0 V' |- V )0) (A0 : obCoMod) (A : obCoMod)
       (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
     forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
     forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
       ( ( v0 o> log.-(0 _ & v )1 ) o>| a_ o>CoMod a' )
         ~~~ ( v0 o>| ( v o>' a_ ) o>CoMod a'
               : 'CoMod(0 WV' |- [0 A0 ~> A' ]0)0 )

 | CoMod_arrowPost :
     forall (V : obV log) (A0 : obCoMod) (A : obCoMod) (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
     forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obCoMod)
       (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
     forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
       ( ( w0 o> log.-(1 w & _ )0 ) o>| a_ o>CoMod a' )
         ~~~ ( w0 o>| a_ o>CoMod ( w o>' a' )
               : 'CoMod(0 W'V |- [0 A0 ~> A' ]0)0 )

 | Limitator_arrowLog :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u : V(0 U' |- U )0) U'' (u' : V(0 U'' |- U' )0),
       ((u' o> u) o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>)
         ~~~ ( u' o>' (u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>)
               : 'CoMod(0 U'' |- [0 L ~> Lim0 func0 ]0)0 )

 | Project_Dom_arrowLog :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
     forall UC UC' (uc' : V(0 UC' |- UC )0) (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
       ((uc' o> uc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
         ~~~ ( uc' o>' (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC' |- [0 Lim0 func0 ~> B ]0 )0 )

 | Project_Codom_arrowLog :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
     forall UC UC' (uc' : V(0 UC' |- UC )0) (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
       ((uc' o> uc) o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
         ~~~ ( uc' o>' (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC' |- [0 Lim0 func0 ~> B ]0 )0 )

 | Project_Dom_arrow :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U U' (u : V(0 U' |- U )0) B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
     forall UC (uc : V(0 UC |- (0 U' & context0 IndexDom )0 )0),
       ((uc o> log.-(1 u & _ )0) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
         ~~~ (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>' b)
              : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0)

 | Project_Codom_arrow :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U U' (u : V(0 U' |- U )0) B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
     forall UC (uc : V(0 UC |- (0 U' & context0 IndexCodom )0 )0),
       ((uc o> log.-(1 u & _ )0) o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
         ~~~ (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>' b)
              : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0)

 | PolyV_CoMod_unit :
     forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
       ( a ) ~~~ ( log.-1 o>' a
                   : 'CoMod(0 V |- [0 A1 ~> A2 ]0)0 )

 | CoMod_unit :
     forall (A : obCoMod) (V : obV log) (v : V(0 V |- log.-I )0)
       (W : obV log) (A' : obCoMod) (a : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
     forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
       ( ( v0 o> log.-(0 W & v )1 o> desIdenObRK ) o>' a )
         ~~~ ( v0 o>| ( v o>| uCoMod ) o>CoMod a
               : 'CoMod(0 WV |- [0 A ~> A' ]0)0 )

 | CoMod_inputUnitCoMod :
     forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0),
     forall (W : obV log) (w : V(0 W |- log.-I )0),
     forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
       ( ( w0 o> log.-(1 w & V )0 o> desIdenObLK ) o>' b )
         ~~~  ( w0 o>| b o>CoMod ( w o>| uCoMod )
                : 'CoMod(0 WV |- [0 B ~> A ]0)0 )

 (* non for reduction *)
 | CoMod_morphism :
     forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0)
       (W_ : obV log) (A' : obCoMod) (a_ : 'CoMod(0 W_ |- [0 A ~> A' ]0 )0)
       (W' : obV log) (A'' : obCoMod) (a' : 'CoMod(0 W' |- [0 A' ~> A'' ]0 )0),
     forall (W_V : obV log) (v : V(0 W_V |- (0 W_ & V )0 )0),
     forall (W'W_V : obV log) (v0 : V(0 W'W_V |- (0 W' & W_V )0 )0),
       ( ( v0 o> (0 W' & v )1 o> Assoc ) o>| b o>CoMod ( log.-1 o>| a_ o>CoMod a' ) )
         ~~~ ( v0 o>| ( v o>| b o>CoMod a_ ) o>CoMod a'
               : 'CoMod(0 W'W_V |- [0 B ~> A'' ]0)0 )

 | Limitator_morphism :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u : V(0 U' |- U )0),
     forall T L' (l : 'CoMod(0 T |- [0 L' ~> L ]0 )0),
     forall U'T (u't : V(0 U'T |- (0 U' & T )0 )0),
       let l_o_f_IndexDom := ((Assoc_Rev o> (0 _ & perm )1 o> Assoc) o>| l o>CoMod f_IndexDom) in
       let l_o_f_IndexCodom := ((Assoc_Rev o> (0 _ & perm )1 o> Assoc) o>| l o>CoMod f_IndexCodom) in
       ((u't o> (1 u & _ )0) o>| << l_o_f_IndexDom , l_o_f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>)
         ~~~ (u't o>| l o>CoMod (u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>)
              : 'CoMod(0 U'T |- [0 L' ~> Lim0 func0 ]0)0)

 | Project_Dom_morphism :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
     forall U' B' (b' : 'CoMod(0 U' |- [0 B ~> B' ]0 )0),
     forall UC (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
     forall U'UC (u'uc : V(0 U'UC |- (0 U' & UC )0 )0),
       ( (u'uc o> (0 U' & uc )1 o> Assoc)
           o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod ((log.-1) o>| b o>CoMod b')  )
         ~~~ ( u'uc o>| (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) o>CoMod b' )

 | Project_Codom_morphism :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
     forall U' B' (b' : 'CoMod(0 U' |- [0 B ~> B' ]0 )0),
     forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
     forall U'UC (u'uc : V(0 U'UC |- (0 U' & UC )0 )0),
       ((u'uc o> (0 U' & uc )1 o> Assoc)
          o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod ((log.-1) o>| b o>CoMod b') )
         ~~~ ( u'uc o>| (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) o>CoMod b' )

 (* for intermediate reduction only, not for intermediate solution *)
 | Limitator_cone :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u : V(0 U' |- U )0),
       ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )
         ~~~ ( u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>
               : 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 )

 (* not for intermediate reduction, not for intermediate solution, for sense only  *)
 | Limitator_cone_rev :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u : V(0 U' |- U )0),
       ( u o>| << f_IndexDom , ( ((0 _ & context1 (ReindexZeros (log.-1)) )1 o> Assoc o> (1 perm & _ )0 o> Assoc_Rev) o>| f_IndexDom o>CoMod func1_ReindexZeros ) @ func1_ReindexZeros , func1_ReindexData >> )
         ~~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>
               : 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 )

 (* for intermediate reduction only, not for intermediate solution *)
 | Project_cone_ReindexZeros :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0)0),
     forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
       ( (uc o> (0 _ & context1 (ReindexZeros (log.-1)) )1 o> Assoc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (log.-1 o>| func1_ReindexZeros o>CoMod b) )
         ~~~ ( (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0)0 ) 

 (* not for intermediate solution *)
 | Project_cone_ReindexData :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0)0),
     forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
       ( (uc o> (0 _ & context1 (ReindexData (log.-1)) )1 o> Assoc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (log.-1 o>| func1_ReindexData o>CoMod b) )
         ~~~ ( (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0)0 ) 
         
 (* alternative, for intermediate solution only *)  
 (*  | Project_cone :
      forall (func0 : obIndexer -> obCoMod)
        (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
      forall UC (uc : V(0 UC |- log.-(0 IndexerMultiplicity & context0 IndexDom )0)0),
        ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (func1_ReindexZeros) )
          ~~~ ( ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (func1_ReindexData) )
                : 'CoMod(0 UC |- [0 Lim0 func0 ~> func0 IndexCodom ]0)0 ) *)

 (*  may or may not be reduced , and  for sense only , has alternative formulation for intermediate solution and final solution *)  
 | Limitator_Project :
     forall (func0 : obIndexer -> obCoMod) (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U (u : V(0 U |- log.-I )0),
       let Project_IndexDom_Id := ((log.-1) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexDom))) in
       let Project_IndexCodom_Id := ((log.-1) o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexCodom))) in
       forall U' (u' : V(0 U' |- U )0),
         ( (u' o> u) o>| @ uCoMod (Lim0 func0) )
           ~~~ ( u' o>| << Project_IndexDom_Id , Project_IndexCodom_Id @ func1_ReindexZeros , func1_ReindexData >>
                 : 'CoMod(0 U' |- [0 Lim0 func0 ~> Lim0 func0 ]0)0 )

 | Project_Dom_Limitator :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u : V(0 U' |- U )0),
     forall UB B (b : 'CoMod(0 UB |- [0 func0 IndexDom ~> B ]0 )0),
     forall UBC (u'c : V(0 UBC |- (0 UB & context0 IndexDom )0 )0),
     forall UBCU' (u'cu : V(0 UBCU' |- (0 UBC & U' )0)0),
       ( (u'cu o> (0 _ & u )1 o> (1 u'c & _ )0 o> Assoc_Rev o> (0 _ & perm )1) o>| f_IndexDom o>CoMod b )
         ~~~ ( u'cu o>| (u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>) o>CoMod ( (u'c o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) : 'CoMod(0 _ |- [0 Lim0 func0 ~> B ]0)0 )
               : 'CoMod(0 UBCU' |- [0 L ~> B ]0)0 )

 | Project_Codom_Limitator :
     forall (func0 : obIndexer -> obCoMod)
       (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
     forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
       (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
     forall U' (u : V(0 U' |- U )0),
     forall UB B (b : 'CoMod(0 UB |- [0 func0 IndexCodom ~> B ]0 )0),
     forall UBC (u'c : V(0 UBC |- (0 UB & context0 IndexCodom )0 )0),
     forall UBCU' (u'cu : V(0 UBCU' |- (0 UBC & U' )0)0),
       ( (u'cu o> (0 _ & u )1 o> (1 u'c & _ )0 o> Assoc_Rev o> (0 _ & perm )1) o>| f_IndexCodom o>CoMod b )
         ~~~ ( u'cu o>| (u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>) o>CoMod (u'c o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) )

 where "f2 ~~~ f1" := (@convCoMod _ _ _ f2 f1) : erased_scope.

 Hint Constructors convCoMod.
 Hint Extern 4 (_ ~~?lo` _) => eapply (@ReflV lo _).
 Ltac rewriterCoMod := repeat match goal with | [ HH : @eq (CoMod00 _ _ _) _ _  |- _ ] =>  try rewrite -> HH in *; clear HH end. 
 
 Module Erase.

  Parameter erase0 : LIMIT.obCoMod -> ERASED.obCoMod.

  (* alternatively, equation because no dependent type *)
  Inductive erase0_specif : LIMIT.obCoMod -> ERASED.obCoMod -> Prop :=
  | erase0_Lim0 :
    forall (func0 : obIndexer -> LIMIT.obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0 %lim),
      erase0_specif (LIMIT.Lim0 func1_ReindexZeros func1_ReindexData) (ERASED.Lim0 (fun A => erase0 (func0 A))).

  Parameter erase0P : forall A : LIMIT.obCoMod, erase0_specif A (erase0 A).
  
  Parameter erase1 : forall (V : obV log) (A1 A2 : LIMIT.obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %lim -> 'CoMod(0 V |- [0 erase0 A1 ~> erase0 A2 ]0 )0 %erased.

  Reserved Notation "f2 =e f1"  (at level 70).

  Inductive erase1_specif : forall (V : obV log) (A1 A2 : LIMIT.obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %lim -> forall erase0_A1 erase0_A2, 'CoMod(0 V |- [0 erase0_A1 ~> erase0_A2 ]0 )0 %erased -> Prop :=

  | erase1_PolyV_CoMod : forall (V V' : obV log),
      forall (v : V(0 V' |- V )0), forall (A1 A2 : LIMIT.obCoMod) (a: 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %lim),
          ( v o>' a )%lim
          =e ( v o>' erase1 a :
                 'CoMod(0 V' |- [0 erase0 A1 ~> erase0 A2 ]0)0 )%erased

  | erase1_UnitCoMod :
    forall (V : obV log), forall (A : LIMIT.obCoMod) (v : V(0 V |- log.-I )0),
          ( v o>| @ uCoMod A )%lim
          =e ( v o>| @ uCoMod (erase0 A)
               : 'CoMod(0 V |- [0 erase0 A ~> erase0 A ]0)0 )%erased

  | erase1_PolyCoMod : forall (V : obV log) (A2 : LIMIT.obCoMod) (A1 : LIMIT.obCoMod)
                                 (a_ : 'CoMod(0 V |- [0 A2 ~> A1 ]0 )0 %lim),
      forall A1' : LIMIT.obCoMod, forall (W WV : obV log),
          forall (wv : V(0 WV |- (0 W & V )0 )0) (a' : 'CoMod(0 W |- [0 A1 ~> A1' ]0 )0 %lim),
            (wv o>| a_ o>CoMod a')%lim
            =e ( (wv o>| erase1 a_ o>CoMod erase1 a' )%erased :
                   'CoMod(0 WV |- [0 erase0 A2 ~> erase0 A1' ]0)0)

  | erase1_Limitator :
    forall (func0 : obIndexer -> LIMIT.obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0 %lim),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0 %lim)
      (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0 %lim)
      (f_cone : cone func1_ReindexZeros func1_ReindexData f_IndexDom f_IndexCodom),
    forall U' (u : V(0 U' |- U )0),
      ( u o>| << f_IndexDom , f_IndexCodom @ f_cone>> )%lim
      =e ( u o>| << erase1 f_IndexDom , erase1 f_IndexCodom @ erase1 func1_ReindexZeros , erase1 func1_ReindexData >>
           : 'CoMod(0 U' |- [0 erase0 L ~> Lim0 (fun A => erase0 (func0 A)) ]0)0 (* /!\ else higher-order unification behind /!\ *) ) %erased

  | erase1_Project_Dom :
    forall (func0 : obIndexer -> LIMIT.obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0 %lim),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0 %lim),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0 ),
      ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )%lim
      =e ( uc o>| ~_IndexDom @ (erase1 func1_ReindexZeros) , (erase1 func1_ReindexData) o>CoMod (erase1 b)
           : 'CoMod(0 UC |- [0 Lim0 (fun A => erase0 (func0 A)) ~> erase0 B ]0)0 (* /!\ else higher-order unification behind /!\ *) )%erased

  | erase1_Project_Codom :
    forall (func0 : obIndexer -> LIMIT.obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0 %lim),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0 %lim),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      ( uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )%lim
      =e ( uc o>| ~_IndexCodom @ (erase1 func1_ReindexZeros) , (erase1 func1_ReindexData) o>CoMod (erase1 b)
           : 'CoMod(0 UC |- [0 Lim0 (fun A => erase0 (func0 A)) ~> erase0 B ]0)0 (* /!\ else higher-order unification behind /!\ *) )%erased
  
  where "f2 =e f1" := (@erase1_specif _ _ _ f2 _ _ f1) : erased_scope.

  Module Export Ex_Notations.
    Notation "f2 =e f1" := (@erase1_specif _ _ _ f2 _ _ f1) : erased_scope.
    Hint Constructors convCoMod.
  End Ex_Notations.

  Parameter erase1P : forall (V : obV log) (A1 A2 : LIMIT.obCoMod)
                        (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %lim),
      erase1_specif a (erase1 a).

  Parameter convCoMod_eraseP : forall (V : obV log) (A1 A2 : LIMIT.obCoMod)
                       (f : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %lim),
      forall (A1'0 A2'0 : LIMIT.obCoMod) (f' : 'CoMod(0 V |- [0 A1'0 ~> A2'0 ]0 )0 %lim),
      forall erase0_A1_A1'0 erase0_A2_A2'0 (erase1_f erase1_f' : 'CoMod(0 V |- [0 erase0_A1_A1'0 ~> erase0_A2_A2'0 ]0 )0 %erased),
        erase1_specif f erase1_f -> erase1_specif f' erase1_f' ->
        (f ~~~ f')%lim <-> (erase1_f ~~~ erase1_f')%erased.
  
  End Erase.
  
  Module Red.
    
  Reserved Notation "f2 <~~ f1" (at level 70).

  Inductive convCoMod : forall (V : obV log) (A1 A2 : obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=

  | CoMod_TransV : forall (V : obV log) (A1 A2 : obCoMod)
               (uTrans a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      uTrans <~~ a -> forall (a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        a' <~~ uTrans -> a' <~~ a

  | PolyV_CoMod_cong : forall (A1 A2 : obCoMod) (V V' : obV log) (v v' : V(0 V' |- V )0)
                                 (a a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      v' ~~ v -> a' <~~ a -> ( v' o>' a' ) <~~ ( v o>' a )

  | CoMod_cong_Pre :
      forall (V : obV log) (A A' : obCoMod) (a_ a_0 : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obCoMod) (a' : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
        v' ~~ v -> a_0 <~~ a_ -> ( v' o>| a_0 o>CoMod a' ) <~~ ( v o>| a_ o>CoMod a' )

  | CoMod_cong_Post :
      forall (V : obV log) (A A' : obCoMod) (a_ : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obCoMod) (a' a'0 : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
        v' ~~ v -> a'0 <~~ a' -> ( v' o>| a_ o>CoMod a'0 ) <~~ ( v o>| a_ o>CoMod a' )

  | Limitator_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
      (f_IndexCodom f'_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom <~~ f_IndexDom) -> (f'_IndexCodom <~~ f_IndexCodom) ->
      ( u0 o>| << f'_IndexDom , f'_IndexCodom @ func1_ReindexZeros , func1_ReindexData >> ) <~~ ( u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >> )

  | Limitator_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom <~~ f_IndexDom) ->
      ( u0 o>| << f'_IndexDom @ func1_ReindexZeros , func1_ReindexData >> ) <~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

  | Limitator_cong_Diagram :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
      (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u ->
      (func1'_ReindexZeros <~~ func1_ReindexZeros) ->
      (func1'_ReindexData <~~ func1_ReindexData) ->
      ( u0 o>| << f_IndexDom , f_IndexCodom @ func1'_ReindexZeros , func1'_ReindexData >> ) <~~ ( u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >> )

  | Limitator_Dom_cong_Diagram :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u ->
      (func1'_ReindexZeros <~~ func1_ReindexZeros) ->
      (func1'_ReindexData <~~ func1_ReindexData) ->
      ( u0 o>| << f_IndexDom @ func1'_ReindexZeros , func1'_ReindexData >> ) <~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

  | Project_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc -> b0 <~~ b ->
      ( uc0 o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b0 ) <~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  | Project_Codom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      uc0 ~~ uc -> b0 <~~ b ->
      ( uc0 o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b0 )
        <~~ ( uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  | Project_Dom_cong_Diagram :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc ->
      (func1'_ReindexZeros <~~ func1_ReindexZeros) ->
      (func1'_ReindexData <~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexDom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b ) <~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  | Project_Codom_cong_Diagram :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      uc0 ~~ uc ->
      (func1'_ReindexZeros <~~ func1_ReindexZeros) ->
      (func1'_ReindexData <~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexCodom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b )
        <~~ ( uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  (* for intermediate reduction only, not for intermediate solution, for sense only *)
  | Limitator_cone :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0)
    (f_IndexCodom : 'CoMod(0 (0 U & context0 IndexCodom )0 |- [0 L ~> func0 IndexCodom ]0 )0),
    forall U' (u : V(0 U' |- U )0),
      ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )
        <~~ ( u o>| << f_IndexDom , f_IndexCodom @ func1_ReindexZeros , func1_ReindexData >>
               : 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 )

  | Project_cone_ReindexZeros :
      forall (func0 : obIndexer -> obCoMod)
        (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexCodom ~> B ]0)0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexCodom )0 )0),
      ( (uc o> (0 _ & context1 (ReindexZeros (log.-1)) )1 o> Assoc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (log.-1 o>| func1_ReindexZeros o>CoMod b) )
        <~~ ( (uc o>| ~_IndexCodom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
              : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0)0 ) 

  where "f2 <~~ f1" := (@convCoMod _ _ _ f2 f1) : erased_scope.

  Module Export Ex_Notations.
    Notation "f2 <~~ f1" := (@convCoMod _ _ _ f2 f1) : erased_scope.
    Hint Constructors convCoMod.
  End Ex_Notations.
  
  Lemma Red_convMod_convMod :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod) (aDeg a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %erased),
      (aDeg <~~ a) %erased -> (aDeg ~~~ a) %erased.
  Proof.
    move => V A1 A2 aDeg a. elim; cbn zeta; eauto.
  Qed.

  Notation max m n := ((m + (Nat.sub n m))%coq_nat).

  Definition grade :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod), 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %erased -> nat.
  Proof.
    move => V A1 A2 a; elim : V A1 A2 / a.
    - intros; refine (S _); assumption. (* PolyV_CoMod *)
    - intros; exact (S (S O)). (* UnitCoMod *)
    - move => ? ? ? a_ grade_a_ ? ? ? ? a' grade_a';
               refine (S  (S (grade_a_ + grade_a')%coq_nat)). (* PolyCoMod *)
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U L f_IndexDom IH_f_IndexDom f_IndexCodom IH_f_IndexCodom U' u.  (* Limitator *)
      refine (( (S (S (S ( max ( IH_f_IndexDom ) ( IH_f_IndexCodom ))))) + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U L f_IndexDom IH_f_IndexDom U' u.  (* Limitator_Dom *)
      refine (( (S (S ( (* max *) ( IH_f_IndexDom ) ))) + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U B b IH_b UC uc.  (* Project_Dom  *)
      refine (( (S (S IH_b))  + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U B b IH_b UC uc.  (* Project_Codom  *)
      refine ( (( (S (S (S   (S (S (IH_b )%coq_nat))))) + IH_func1_ReindexZeros)%coq_nat + IH_func1_ReindexZeros)%coq_nat + IH_func1_ReindexData)%coq_nat.
  Defined.

  Lemma degrade :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod) (aDeg a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %erased),
      (aDeg <~~ a) %erased -> ((grade aDeg) < (grade a))%coq_nat. 
  Proof.
    (move => V A1 A2 aDeg a red_a); elim : V A1 A2 aDeg a / red_a;
      try solve [ simpl; intros;
                  abstract intuition Omega.omega ].
  Qed.

  End Red.
  
  Module DISSOLUTION.

  Delimit Scope dissol_scope with dissol.
  Open Scope dissol.

  Reserved Notation "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0" (at level 25, format "''CoMod' (0  V  |-  [0  A1  ~>  A2  ]0 )0").

  Inductive CoMod00 : obV log -> obCoMod -> obCoMod -> Type :=
    | PolyV_CoMod : forall (V V' : obV log),
      V(0 V' |- V )0 -> forall (A1 A2 : obCoMod), 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 ->
                                         'CoMod(0 V' |- [0 A1 ~> A2 ]0 )0
    | UnitCoMod : forall (V : obV log), forall {A : obCoMod}
        ,  V(0 V |- log.-I )0 -> 'CoMod(0 V |- [0 A ~> A ]0 )0

    | PolyCoMod : forall (V : obV log) (A2 : obCoMod) (A1 : obCoMod)
    , 'CoMod(0 V |- [0 A2 ~> A1 ]0 )0 -> forall A1' : obCoMod, forall (W WV : obV log),
          V(0 WV |- (0 W & V )0 )0 ->
          'CoMod(0 W |- [0 A1 ~> A1' ]0 )0 -> 'CoMod(0 WV |- [0 A2 ~> A1' ]0 )0

    | Limitator_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
      forall U', V(0 U' |- U )0 -> 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 

    | Project_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B, 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0 -> forall UC, V(0 UC |- (0 U & context0 IndexDom )0 )0 ->
                                                           'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0

  where "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0" := (@CoMod00 V A1 A2) : dissol_scope.

  Definition PolyV_CoMod_rewrite V V' A1 A2 v a :=
    (@PolyV_CoMod V V' v A1 A2 a).
  Notation "v o>' a" := (@PolyV_CoMod_rewrite _ _ _ _ v a)
                          (at level 25, right associativity, format "v  o>'  a") : dissol_scope.
  Notation "v o>| 'uCoMod'" := (@UnitCoMod _ _ v)(at level 25) : dissol_scope.
  Notation "v o>| @ 'uCoMod' A" :=
    (@UnitCoMod _ A v) (at level 25, only parsing) : dissol_scope.
  Definition PolyCoMod_rewrite V A2 A1 A1' W WV wv a_ a' :=
    (@PolyCoMod V A2 A1 a_ A1' W WV wv a').
  Notation "v o>| a_ o>CoMod a'" :=
    (@PolyCoMod_rewrite _ _ _ _ _ _ v a_ a')
      (at level 25, right associativity, a_ at next level, format "v  o>|  a_  o>CoMod  a'") : dissol_scope.

  Notation "u o>| << f_ @ func1_ReindexZeros , func1_ReindexData >>" :=
    (@Limitator_Dom _ func1_ReindexZeros func1_ReindexData _ _ f_ _ u) (at level 0) : dissol_scope.
  Notation "u o>| << f_ >>" :=
    (@Limitator_Dom _ _ _ _ _ f_ _ u) (at level 0) : dissol_scope.

  Notation "uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b" :=
    (@Project_Dom _ func1_ReindexZeros func1_ReindexData _ _ b _ uc) (at level 25) : dissol_scope.
  Notation "uc o>| ~_IndexDom o>CoMod b" :=
    (@Project_Dom _ _ _ _ _ b _ uc) (at level 25) : dissol_scope.
  
  Reserved Notation "f2 ~~~ f1"  (at level 70).

  Inductive convCoMod : forall (V : obV log) (A1 A2 : obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=

  | CoMod_ReflV : forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      a ~~~ a

  | CoMod_TransV : forall (V : obV log) (A1 A2 : obCoMod)
               (uTrans a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      uTrans ~~~ a -> forall (a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        a' ~~~ uTrans -> a' ~~~ a

  | CoMod_SymV : forall (V : obV log) (A1 A2 : obCoMod) (a a' : 'CoMod(0 V |- [0 A1 ~> A2]0 )0),
      a ~~~ a' -> a' ~~~ a

  | PolyV_CoMod_cong : forall (A1 A2 : obCoMod) (V V' : obV log) (v v' : V(0 V' |- V )0)
                                 (a a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      v' ~~ v -> a' ~~~ a -> ( v' o>' a' ) ~~~ ( v o>' a )

  | UnitCoMod_cong : forall (V : obV log), forall {A : obCoMod} (v v' : V(0 V |- log.-I )0),
        v' ~~ v -> v' o>| @uCoMod A ~~~ v o>| @uCoMod A

  | CoMod_cong :
      forall (V : obV log) (A A' : obCoMod) (a_ a_0 : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obCoMod) (a' a'0 : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
        v' ~~ v -> a_0 ~~~ a_ -> a'0 ~~~ a' -> ( v' o>| a_0 o>CoMod a'0 ) ~~~ ( v o>| a_ o>CoMod a' )

  | Limitator_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom ~~~ f_IndexDom) ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( u0 o>| << f'_IndexDom @ func1'_ReindexZeros , func1'_ReindexData >> ) ~~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

  | Project_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc -> b0 ~~~ b ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexDom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b0 ) ~~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  | PolyV_CoMod_arrowLog :
      forall (V'' V' : obV log) (v' : V(0 V'' |- V' )0) (V : obV log)
        (v : V(0 V' |- V )0) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v' o> v ) o>' a )
          ~~~ ( v' o>' ( v o>' a )
                : 'CoMod(0 V'' |- [0 A1 ~> A2 ]0)0 )

  | UnitCoMod_arrowLog : forall (V V' : obV log) (A : obCoMod) (v : V(0 V |- log.-I )0)
                                   (v' : V(0 V' |- V )0),
      ( ( v' o> v ) o>| @uCoMod A )
        ~~~ (v' o>' (v o>| @uCoMod A)
             : 'CoMod(0 V' |- [0 A ~> A ]0)0 )

  | CoMod_arrowLog :
      forall (V : obV log) (A0 : obCoMod) (A : obCoMod)
        (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
      forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
        ( ( v0 o> v ) o>| a_ o>CoMod a' )
          ~~~ ( v0 o>' ( v o>| a_ o>CoMod a' )
                : 'CoMod(0 WV0 |- [0 A0 ~> A' ]0)0 )

  | CoMod_arrowPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0) (A0 : obCoMod) (A : obCoMod)
        (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( v0 o> log.-(0 _ & v )1 ) o>| a_ o>CoMod a' )
          ~~~ ( v0 o>| ( v o>' a_ ) o>CoMod a'
                : 'CoMod(0 WV' |- [0 A0 ~> A' ]0)0 )

  | CoMod_arrowPost :
      forall (V : obV log) (A0 : obCoMod) (A : obCoMod) (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obCoMod)
        (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
        ( ( w0 o> log.-(1 w & _ )0 ) o>| a_ o>CoMod a' )
          ~~~ ( w0 o>| a_ o>CoMod ( w o>' a' )
                : 'CoMod(0 W'V |- [0 A0 ~> A' ]0)0 )

  | Limitator_Dom_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u : V(0 U' |- U )0) U'' (u' : V(0 U'' |- U' )0),
        ((u' o> u) o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
          ~~~ ( u' o>' (u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
                : 'CoMod(0 U'' |- [0 L ~> Lim0 func0 ]0)0 )

  | Project_Dom_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
        forall UC UC' (uc' : V(0 UC' |- UC )0) (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
          ((uc' o> uc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            ~~~ ( uc' o>' (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC' |- [0 Lim0 func0 ~> B ]0 )0 )

  | Project_Dom_arrow :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U U' (u : V(0 U' |- U )0) B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
        forall UC (uc : V(0 UC |- (0 U' & context0 IndexDom )0 )0),
          ((uc o> log.-(1 u & _ )0) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            ~~~ (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>' b)
                 : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0)

  | PolyV_CoMod_unit :
      forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( a ) ~~~ ( log.-1 o>' a
                    : 'CoMod(0 V |- [0 A1 ~> A2 ]0)0 )

  | CoMod_unit :
      forall (A : obCoMod) (V : obV log) (v : V(0 V |- log.-I )0)
        (W : obV log) (A' : obCoMod) (a : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
        ( ( v0 o> log.-(0 W & v )1 o> desIdenObRK ) o>' a )
          ~~~ ( v0 o>| ( v o>| uCoMod ) o>CoMod a
                : 'CoMod(0 WV |- [0 A ~> A' ]0)0 )

  | CoMod_inputUnitCoMod :
      forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (w : V(0 W |- log.-I )0),
      forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
        ( ( w0 o> log.-(1 w & V )0 o> desIdenObLK ) o>' b )
          ~~~  ( w0 o>| b o>CoMod ( w o>| uCoMod )
                 : 'CoMod(0 WV |- [0 B ~> A ]0)0 )

  (* non for reduction *)
  | CoMod_morphism :
      forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0)
        (W_ : obV log) (A' : obCoMod) (a_ : 'CoMod(0 W_ |- [0 A ~> A' ]0 )0)
        (W' : obV log) (A'' : obCoMod) (a' : 'CoMod(0 W' |- [0 A' ~> A'' ]0 )0),
      forall (W_V : obV log) (v : V(0 W_V |- (0 W_ & V )0 )0),
      forall (W'W_V : obV log) (v0 : V(0 W'W_V |- (0 W' & W_V )0 )0),
        ( ( v0 o> (0 W' & v )1 o> Assoc ) o>| b o>CoMod ( log.-1 o>| a_ o>CoMod a' ) )
          ~~~ ( v0 o>| ( v o>| b o>CoMod a_ ) o>CoMod a'
                : 'CoMod(0 W'W_V |- [0 B ~> A'' ]0)0 )

  | Limitator_Dom_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u : V(0 U' |- U )0),
    forall T L' (l : 'CoMod(0 T |- [0 L' ~> L ]0 )0),
    forall U'T (u't : V(0 U'T |- (0 U' & T )0 )0),
      let l_o_f_IndexDom := ((Assoc_Rev o> (0 _ & perm )1 o> Assoc) o>| l o>CoMod f_IndexDom) in
        ((u't o> (1 u & _ )0) o>| << l_o_f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
          ~~~ (u't o>| l o>CoMod (u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
               : 'CoMod(0 U'T |- [0 L' ~> Lim0 func0 ]0)0)

  | Project_Dom_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall U' B' (b' : 'CoMod(0 U' |- [0 B ~> B' ]0 )0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
    forall U'UC (u'uc : V(0 U'UC |- (0 U' & UC )0 )0),
      ((u'uc o> (0 U' & uc )1 o> Assoc)
         o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod ((log.-1) o>| b o>CoMod b') )
        ~~~ ( u'uc o>| (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) o>CoMod b'
              : 'CoMod(0 U'UC |- [0 Lim0 func0 ~> B' ]0)0 )

  (* non for reduction , for sense only *)  
  | Project_Dom_cone :
      forall (func0 : obIndexer -> obCoMod)
        (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
      forall UC (uc : V(0 UC |- log.-(0 IndexerMultiplicity & context0 IndexDom )0)0),
        ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (func1_ReindexZeros) )
          ~~~ ( ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (func1_ReindexData) )
                : 'CoMod(0 UC |- [0 Lim0 func0 ~> func0 IndexCodom ]0)0 ) 

  (* non for reduction , for sense only *)  
  | Limitator_Dom_Project_Dom :
    forall (func0 : obIndexer -> obCoMod) (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U (u : V(0 U |- log.-I )0),
      let Project_Dom_Unit_Id := ((log.-1) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexDom))) in
      forall U' (u' : V(0 U' |- U )0),
        ( (u' o> u) o>| @ uCoMod (Lim0 func0) )
          ~~~ ( u' o>| << Project_Dom_Unit_Id @ func1_ReindexZeros , func1_ReindexData >>
                : 'CoMod(0 U' |- [0 Lim0 func0 ~> Lim0 func0 ]0)0 )

  | Project_Dom_Limitator_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u : V(0 U' |- U )0),
    forall UB B (b : 'CoMod(0 UB |- [0 func0 IndexDom ~> B ]0 )0),
    forall UBC (u'c : V(0 UBC |- (0 UB & context0 IndexDom )0 )0),
    forall UBCU' (u'cu : V(0 UBCU' |- (0 UBC & U' )0)0),
      ( (u'cu o> (0 _ & u )1 o> (1 u'c & _ )0 o> Assoc_Rev o> (0 _ & perm )1) o>| f_IndexDom o>CoMod b )
        ~~~ ( u'cu o>| (u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>) o>CoMod (u'c o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
              : 'CoMod(0 UBCU' |- [0 L ~> B ]0)0 )
 
  where "f2 ~~~ f1" := (@convCoMod _ _ _ f2 f1) : dissol_scope.

  Hint Constructors convCoMod.

  Ltac rewriterCoMod := repeat match goal with | [ HH : @eq (CoMod00 _ _ _) _ _  |- _ ] =>  try rewrite -> HH in *; clear HH end.

  Module DisSolve.
    
    Import ERASED.Erase.Ex_Notations.
    Import ERASED.Red.Ex_Notations.

    Definition toErased : forall (V : obV log) (A1 A2 : ERASED.obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 % dissol -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %erased.
    Admitted.
    
    Definition disSolve :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %erased),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol.
    Admitted.

    Lemma disSolveP1 :
      forall (V : obV log) (A1 A2 : ERASED.obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %erased),
        ( (toErased (disSolve a)) <~~ a )%erased \/ ( (toErased (disSolve a)) = a ) .
    Admitted.

    Lemma disSolveP2 : forall (V : obV log) (erase0_A1_A1'0 erase0_A2_A2'0 : ERASED.obCoMod) (erase1_a erase1_a' : 'CoMod(0 V |- [0 erase0_A1_A1'0 ~> erase0_A2_A2'0 ]0 )0 %erased),
        forall (A1 A2 : LIMIT.obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %lim),
          (a =e erase1_a) %erased ->
          forall (A1'0 A2'0 : LIMIT.obCoMod) (a' : 'CoMod(0 V |- [0 A1'0 ~> A2'0 ]0 )0 %lim),
            (a' =e erase1_a') %erased ->
        (erase1_a ~~~ erase1_a') %erased <-> (disSolve erase1_a ~~~ disSolve erase1_a') %dissol.
    Admitted.

  End DisSolve.

  Module Red.
    
  Reserved Notation "f2 <~~ f1" (at level 70).

  Inductive convCoMod : forall (V : obV log) (A1 A2 : obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=

  | CoMod_TransV : forall (V : obV log) (A1 A2 : obCoMod)
               (uTrans a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      uTrans <~~ a -> forall (a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        a' <~~ uTrans -> a' <~~ a

  | PolyV_CoMod_cong : forall (A1 A2 : obCoMod) (V V' : obV log) (v v' : V(0 V' |- V )0)
                                 (a a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      v' ~~ v -> a' <~~ a -> ( v' o>' a' ) <~~ ( v o>' a )

  | CoMod_cong_Pre :
      forall (V : obV log) (A A' : obCoMod) (a_ a_0 : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obCoMod) (a' : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
        v' ~~ v -> a_0 <~~ a_ -> ( v' o>| a_0 o>CoMod a' ) <~~ ( v o>| a_ o>CoMod a' )

  | CoMod_cong_Post :
      forall (V : obV log) (A A' : obCoMod) (a_ : 'CoMod(0 V |- [0 A ~> A' ]0 )0),
      forall (W : obV log) (A'' : obCoMod) (a' a'0 : 'CoMod(0 W |- [0 A' ~> A'' ]0 )0),
      forall (WV : obV log) (v v' : V(0 WV |- (0 W & V )0 )0),
        v' ~~ v -> a'0 <~~ a' -> ( v' o>| a_ o>CoMod a'0 ) <~~ ( v o>| a_ o>CoMod a' )

  (* ??multiply this congruence into finer congruence reductions?? *)
  | Limitator_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom <~~ f_IndexDom) ->
      ( u0 o>| << f'_IndexDom @ func1_ReindexZeros , func1_ReindexData >> ) <~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

  | Limitator_Dom_cong_Diagram :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u ->
      (func1'_ReindexZeros <~~ func1_ReindexZeros) ->
      (func1'_ReindexData <~~ func1_ReindexData) ->
      ( u0 o>| << f_IndexDom @ func1'_ReindexZeros , func1'_ReindexData >> ) <~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

  (* ~~~~??multiply this congruence into finer congruence reductions?? *)
  | Project_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc -> b0 <~~ b ->
      ( uc0 o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b0 ) <~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  | Project_Dom_cong_Diagram :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc ->
      (func1'_ReindexZeros <~~ func1_ReindexZeros) ->
      (func1'_ReindexData <~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexDom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b ) <~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )

  | PolyV_CoMod_arrowLog :
      forall (V'' V' : obV log) (v' : V(0 V'' |- V' )0) (V : obV log)
        (v : V(0 V' |- V )0) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( ( v' o> v ) o>' a )
          <~~ ( v' o>' ( v o>' a )
                : 'CoMod(0 V'' |- [0 A1 ~> A2 ]0)0 )

  | UnitCoMod_arrowLog : forall (V V' : obV log) (A : obCoMod) (v : V(0 V |- log.-I )0)
                                   (v' : V(0 V' |- V )0),
      ( ( v' o> v ) o>| @uCoMod A )
        <~~ (v' o>' (v o>| @uCoMod A)
             : 'CoMod(0 V' |- [0 A ~> A ]0)0 )

  | CoMod_arrowLog :
      forall (V : obV log) (A0 : obCoMod) (A : obCoMod)
        (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v : V(0 WV |- (0 W & V )0 )0),
      forall (WV0 : obV log) (v0 : V(0 WV0 |- WV )0),
        ( ( v0 o> v ) o>| a_ o>CoMod a' )
          <~~ ( v0 o>' ( v o>| a_ o>CoMod a' )
                : 'CoMod(0 WV0 |- [0 A0 ~> A' ]0)0 )

  | CoMod_arrowPre :
      forall (V V' : obV log) (v : V(0 V' |- V )0) (A0 : obCoMod) (A : obCoMod)
        (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W : obV log) (A' : obCoMod) (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV' : obV log) (v0 : V(0 WV' |- (0 W & V' )0 )0),
        ( ( v0 o> log.-(0 _ & v )1 ) o>| a_ o>CoMod a' )
          <~~ ( v0 o>| ( v o>' a_ ) o>CoMod a'
                : 'CoMod(0 WV' |- [0 A0 ~> A' ]0)0 )

  | CoMod_arrowPost :
      forall (V : obV log) (A0 : obCoMod) (A : obCoMod) (a_ : 'CoMod(0 V |- [0 A0 ~> A ]0 )0),
      forall (W W' : obV log) (w : V(0 W' |- W )0) (A' : obCoMod)
        (a' : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (W'V : obV log) (w0 : V(0 W'V |- (0 W' & V )0 )0),
        ( ( w0 o> log.-(1 w & _ )0 ) o>| a_ o>CoMod a' )
          <~~ ( w0 o>| a_ o>CoMod ( w o>' a' )
                : 'CoMod(0 W'V |- [0 A0 ~> A' ]0)0 )

  | Limitator_Dom_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u : V(0 U' |- U )0) U'' (u' : V(0 U'' |- U' )0),
        ((u' o> u) o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
          <~~ ( u' o>' (u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
                : 'CoMod(0 U'' |- [0 L ~> Lim0 func0 ]0)0 )

  | Project_Dom_arrowLog :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
        forall UC UC' (uc' : V(0 UC' |- UC )0) (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
          ((uc' o> uc) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            <~~ ( uc' o>' (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
               : 'CoMod(0 UC' |- [0 Lim0 func0 ~> B ]0 )0 )

  | Project_Dom_arrow :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U U' (u : V(0 U' |- U )0) B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
        forall UC (uc : V(0 UC |- (0 U' & context0 IndexDom )0 )0),
          ((uc o> log.-(1 u & _ )0) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
            <~~ (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>' b)
                 : 'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0)

  | PolyV_CoMod_unit :
      forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
        ( a ) <~~ ( log.-1 o>' a
                    : 'CoMod(0 V |- [0 A1 ~> A2 ]0)0 )

  | CoMod_unit :
      forall (A : obCoMod) (V : obV log) (v : V(0 V |- log.-I )0)
        (W : obV log) (A' : obCoMod) (a : 'CoMod(0 W |- [0 A ~> A' ]0 )0),
      forall (WV : obV log) (v0 : V(0 WV |- (0 W & V )0 )0),
        ( ( v0 o> log.-(0 W & v )1 o> desIdenObRK ) o>' a )
          <~~ ( v0 o>| ( v o>| uCoMod ) o>CoMod a
                : 'CoMod(0 WV |- [0 A ~> A' ]0)0 )

  | CoMod_inputUnitCoMod :
      forall (V : obV log) (B : obCoMod) (A : obCoMod) (b : 'CoMod(0 V |- [0 B ~> A ]0 )0),
      forall (W : obV log) (w : V(0 W |- log.-I )0),
      forall (WV : obV log) (w0 : V(0 WV |- (0 W & V )0 )0),
        ( ( w0 o> log.-(1 w & V )0 o> desIdenObLK ) o>' b )
          <~~  ( w0 o>| b o>CoMod ( w o>| uCoMod )
                 : 'CoMod(0 WV |- [0 B ~> A ]0)0 )

  (* non for reduction 
  | CoMod_morphism : *)

  | Limitator_Dom_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u : V(0 U' |- U )0),
    forall T L' (l : 'CoMod(0 T |- [0 L' ~> L ]0 )0),
    forall U'T (u't : V(0 U'T |- (0 U' & T )0 )0),
      let l_o_f_IndexDom := ((Assoc_Rev o> (0 _ & perm )1 o> Assoc) o>| l o>CoMod f_IndexDom) in
        ((u't o> (1 u & _ )0) o>| << l_o_f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
          <~~ (u't o>| l o>CoMod (u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>)
               : 'CoMod(0 U'T |- [0 L' ~> Lim0 func0 ]0)0)

  | Project_Dom_morphism :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall U' B' (b' : 'CoMod(0 U' |- [0 B ~> B' ]0 )0),
    forall UC (uc : V(0 UC |- (0 U & context0 IndexDom )0 )0),
    forall U'UC (u'uc : V(0 U'UC |- (0 U' & UC )0 )0),
      ((u'uc o> (0 U' & uc )1 o> Assoc)
         o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod ((log.-1) o>| b o>CoMod b') )
        <~~ ( u'uc o>| (uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b) o>CoMod b'
              : 'CoMod(0 U'UC |- [0 Lim0 func0 ~> B' ]0)0 )

  (* non for reduction , for sense only 
  | Project_Dom_cone : *)

  (* non for reduction , for sense only *)  
  | Limitator_Dom_Project_Dom :
    forall (func0 : obIndexer -> obCoMod) (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U (u : V(0 U |- log.-I )0),
      let Project_Dom_Unit_Id := ((log.-1) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexDom))) in
      forall U' (u' : V(0 U' |- U )0),
        ( (u' o> u) o>| @ uCoMod (Lim0 func0) )
          <~~ ( u' o>| << Project_Dom_Unit_Id @ func1_ReindexZeros , func1_ReindexData >>
                : 'CoMod(0 U' |- [0 Lim0 func0 ~> Lim0 func0 ]0)0 )

  | Project_Dom_Limitator_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u : V(0 U' |- U )0),
    forall UB B (b : 'CoMod(0 UB |- [0 func0 IndexDom ~> B ]0 )0),
    forall UBC (u'c : V(0 UBC |- (0 UB & context0 IndexDom )0 )0),
    forall UBCU' (u'cu : V(0 UBCU' |- (0 UBC & U' )0)0),
      ( (u'cu o> (0 _ & u )1 o> (1 u'c & _ )0 o> Assoc_Rev o> (0 _ & perm )1) o>| f_IndexDom o>CoMod b )
        <~~ ( u'cu o>| (u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >>) o>CoMod (u'c o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b)
              : 'CoMod(0 UBCU' |- [0 L ~> B ]0)0 )
 
  where "f2 <~~ f1" := (@convCoMod _ _ _ f2 f1) : dissol_scope.

  Module Export Ex_Notations.
    Notation "f2 <~~ f1" := (@convCoMod _ _ _ f2 f1) : dissol_scope.
    Hint Constructors convCoMod.
  End Ex_Notations.

  Lemma Red_convMod_convMod :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod) (aDeg a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol),
      (aDeg <~~ a) %dissol -> (aDeg ~~~ a)%dissol.
  Proof.
    move => V A1 A2 aDeg a. elim; cbn zeta; eauto.
  Qed.

  Definition grade :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod), 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol -> nat.
  Proof.
    move => V A1 A2 a; elim : V A1 A2 / a.
    - intros; refine (S _); assumption. (* PolyV_CoMod *)
    - intros; exact (S (S O)). (* UnitCoMod *)
    - move => ? ? ? a_ grade_a_ ? ? ? ? a' grade_a';
               refine (S  (S (grade_a_ + grade_a')%coq_nat)). (* PolyCoMod *)
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U L f_IndexDom IH_f_IndexDom U' u.  (* Limitator_Dom *)
      refine (( (S (S ( (* max *) ( IH_f_IndexDom )))) + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U B b IH_b UC uc.  (* Project_Dom  *)
      refine (( (S (S IH_b))  + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
  Defined.

  Definition gradeMaxCom :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod), 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol -> nat.
  Proof.
    move => V A1 A2 a; elim : V A1 A2 / a.
    - intros; assumption. (* PolyV_CoMod *)
    - intros; exact (O). (* UnitCoMod *)
    - move => ? ? ? a_ gradeCom_a_ ? ? ? v a' gradeCom_a';
               refine (gradeCom_a_ + (gradeCom_a' + (grade ( v o>| a_ o>CoMod a')) )%coq_nat )%coq_nat.
    (* PolyCoMod *)
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U L f_IndexDom IH_f_IndexDom U' u.  (* Limitator_Dom *)
      refine (( ((( (* max *) ( IH_f_IndexDom ) ))) + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
    - intros func0 func1_ReindexZeros IH_func1_ReindexZeros func1_ReindexData  IH_func1_ReindexData U B b IH_b UC uc.  (* Project_Dom  *)
      refine (( ( ( IH_b)) + IH_func1_ReindexZeros )%coq_nat + IH_func1_ReindexData)%coq_nat.
  Defined.

  Definition gradeTotal (V : obV log) (A1 A2 : ERASED.obCoMod) :
    'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol -> nat.
  Proof.
    move => a; refine ( (grade a) + (gradeMaxCom a)  )%coq_nat.
  Defined.

  Lemma degrade :
    forall (V : obV log) (A1 A2 : ERASED.obCoMod) (aDeg a: 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol),
      (aDeg <~~ a) %dissol -> ((grade aDeg) <= (grade a))%coq_nat
                 /\ ( ( (gradeTotal aDeg) < (gradeTotal a) )%coq_nat ).
  Proof.
    (move => V A1 A2 aDeg a red_a); elim : V A1 A2 aDeg a / red_a;
      try solve [ rewrite /gradeTotal /= => * ;
                                           abstract intuition Omega.omega ].
  Qed.

  End Red.

  Module RESOLUTION.

  Delimit Scope sol_scope with sol.
  Open Scope sol.

  Reserved Notation "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0" (at level 25, format "''CoMod' (0  V  |-  [0  A1  ~>  A2  ]0 )0").

  Inductive CoMod00 : obV log -> obCoMod -> obCoMod -> Type :=
    | UnitCoMod : forall (V : obV log), forall {A : obCoMod}
      ,  V(0 V |- log.-I )0 -> 'CoMod(0 V |- [0 A ~> A ]0 )0

    | Limitator_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
      forall U', V(0 U' |- U )0 -> 'CoMod(0 U' |- [0 L ~> Lim0 func0 ]0)0 

    | Project_Dom :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B, 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0 -> forall UC, V(0 UC |- (0 U & context0 IndexDom )0 )0 ->
                                                           'CoMod(0 UC |- [0 Lim0 func0 ~> B ]0 )0

  where "''CoMod' (0 V |- [0 A1 ~> A2 ]0 )0" := (@CoMod00 V A1 A2) : sol_scope.

  Notation "v o>| 'uCoMod'" := (@UnitCoMod _ _ v)(at level 25) : sol_scope.
  Notation "v o>| @ 'uCoMod' A" :=
    (@UnitCoMod _ A v) (at level 25, only parsing) : sol_scope.

  Notation "u o>| << f_ @ func1_ReindexZeros , func1_ReindexData >>" :=
    (@Limitator_Dom _ func1_ReindexZeros func1_ReindexData _ _ f_ _ u) (at level 0) : sol_scope.
  Notation "u o>| << f_ >>" :=
    (@Limitator_Dom _ _ _ _ _ f_ _ u) (at level 0) : sol_scope.

  Notation "uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b" :=
    (@Project_Dom _ func1_ReindexZeros func1_ReindexData _ _ b _ uc) (at level 25) : sol_scope.
  Notation "uc o>| ~_IndexDom o>CoMod b" :=
    (@Project_Dom _ _ _ _ _ b _ uc) (at level 25) : sol_scope.
  
  Reserved Notation "f2 ~~~ f1"  (at level 70).

  (* decidable congruence-style,,, *)
  Inductive convCoMod : forall (V : obV log) (A1 A2 : obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 -> Prop :=

  | CoMod_ReflV : forall (V : obV log) (A1 A2 : obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0),
      a ~~~ a

  | UnitCoMod_cong : forall (V : obV log), forall {A : obCoMod} (v v' : V(0 V |- log.-I )0),
        v' ~~ v -> v' o>| @uCoMod A ~~~ v o>| @uCoMod A

  | Limitator_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U L (f_IndexDom f'_IndexDom : 'CoMod(0 (0 U & context0 IndexDom )0 |- [0 L ~> func0 IndexDom ]0 )0),
    forall U' (u u0 : V(0 U' |- U )0),
      u0 ~~ u -> (f'_IndexDom ~~~ f_IndexDom) ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( u0 o>| << f'_IndexDom @ func1'_ReindexZeros , func1'_ReindexData >> ) ~~~ ( u o>| << f_IndexDom @ func1_ReindexZeros , func1_ReindexData >> )

  | Project_Dom_cong :
    forall (func0 : obIndexer -> obCoMod)
      (func1_ReindexZeros func1_ReindexData func1'_ReindexZeros func1'_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U B (b b0 : 'CoMod(0 U |- [0 func0 IndexDom ~> B ]0 )0),
    forall UC (uc uc0 : V(0 UC |- (0 U & context0 IndexDom )0 )0),
      uc0 ~~ uc -> b0 ~~~ b ->
      (func1'_ReindexZeros ~~~ func1_ReindexZeros) ->
      (func1'_ReindexData ~~~ func1_ReindexData) ->
      ( uc0 o>| ~_IndexDom @ func1'_ReindexZeros , func1'_ReindexData o>CoMod b0 ) ~~~ ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod b )


  (* non for reduction , for sense only *)  
  | Project_Dom_cone :
      forall (func0 : obIndexer -> obCoMod)
        (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
      forall UC (uc uc0 : V(0 UC |- log.-(0 IndexerMultiplicity & context0 IndexDom )0)0),
        uc0 ~~ uc ->
        ( uc0 o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (func1_ReindexZeros) )
          ~~~ ( ( uc o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (func1_ReindexData) )
                : 'CoMod(0 UC |- [0 Lim0 func0 ~> func0 IndexCodom ]0)0 ) 

  (* non for reduction , for sense only *)  
  | Limitator_Dom_Project_Dom' :
    forall (func0 : obIndexer -> obCoMod) (func1_ReindexZeros func1_ReindexData : 'CoMod(0 IndexerMultiplicity |- [0 func0 IndexDom ~> func0 IndexCodom ]0 )0),
    forall U (u : V(0 U |- log.-I )0),
      let Project_Dom_Unit_Id := ((log.-1) o>| ~_IndexDom @ func1_ReindexZeros , func1_ReindexData o>CoMod (u o>| @ uCoMod (func0 IndexDom))) in
      forall U' (u' : V(0 U' |- U )0) (u'u : V(0 U' |- log.-I )0),
        u'u ~~ (u' o> u) ->
        ( (u'u) o>| @ uCoMod (Lim0 func0) )
          ~~~ ( u' o>| << Project_Dom_Unit_Id @ func1_ReindexZeros , func1_ReindexData >>
                : 'CoMod(0 U' |- [0 Lim0 func0 ~> Lim0 func0 ]0)0 )
 
  where "f2 ~~~ f1" := (@convCoMod _ _ _ f2 f1) : sol_scope.

  Hint Constructors convCoMod.

  Module ReSolve.
    
    Import DISSOLUTION.Red.Ex_Notations.

    Definition toDisSolution : forall (V : obV log) (A1 A2 : ERASED.obCoMod),
      'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 % sol -> 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol.
    Admitted.
    
    Definition reSolve :
      forall (V : obV log) (A1 A2 : ERASED.obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol),
        'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %sol.
    Admitted.

    Lemma reSolveP1 :
      forall (V : obV log) (A1 A2 : ERASED.obCoMod) (a : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol),
        ( (toDisSolution (reSolve a)) <~~ a )%dissol \/ ( (toDisSolution (reSolve a)) = a ) .
    Admitted.

    Lemma reSolveP2 :
      forall (V : obV log) (A1 A2 : ERASED.obCoMod) (a a' : 'CoMod(0 V |- [0 A1 ~> A2 ]0 )0 %dissol),
        (a ~~~ a') %dissol <-> (reSolve a ~~~ reSolve a') %sol.
    Admitted.

  End ReSolve.

  End RESOLUTION.

  End DISSOLUTION.

 End ERASED.

End LIMIT.

(**#+END_SRC

Voila. **)
