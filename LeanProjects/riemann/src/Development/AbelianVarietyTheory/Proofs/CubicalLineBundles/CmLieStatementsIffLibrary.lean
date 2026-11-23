import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamF

theorem pnsmulPt_eq_frozen {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} (n : ℕ) (x : T ⟶ G) :
    pnsmulPt n x = Formalism.L2.Pj.abelian₂.pnsmulPt n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pnsmulPt, Formalism.L2.Pj.abelian₂.pnsmulPt, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

@[reducible] def LamObj.toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

@[reducible] def LamObj.ofFrozen (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') : LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

theorem LamObj.ofFrozen_toFrozen (o : LamObj c nΨ n') : LamObj.ofFrozen o.toFrozen = o := rfl

theorem LamObj.toFrozen_ofFrozen (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') : (LamObj.ofFrozen o).toFrozen = o := rfl

theorem rosatiConj_iff_frozen {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) :
    RosatiConj A oa ↔ Formalism.L2.Pj.abelian₂.RosatiConj A oa := by
  simp only [RosatiConj, Formalism.L2.Pj.abelian₂.RosatiConj, pnsmulPt_eq_frozen]

theorem isIsogSum_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.IsIsogSum o.toFrozen ↔ IsIsogSum o := by
  simp only [IsIsogSum, Formalism.L2.Pj.abelian₂.IsIsogSum, pnsmulPt_eq_frozen]
  rfl

theorem polClause_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.PolClause o.toFrozen ↔ PolClause o := by
  simp only [PolClause, Formalism.L2.Pj.abelian₂.PolClause, pnsmulPt_eq_frozen]

theorem fixed_of_lambdaBundle_objectCondition (o : LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    Formalism.L2.Pj.abelian₂.LamObjGood o.toFrozen f La ↔ LamObjGood o f La := by
  unfold LamObjGood Formalism.L2.Pj.abelian₂.LamObjGood
  rw [isIsogSum_toFrozen, polClause_toFrozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen]
  rfl

theorem lambdaBundle_objectCondition_of_fixed (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    LamObjGood (LamObj.ofFrozen o) f La ↔ Formalism.L2.Pj.abelian₂.LamObjGood o f La :=
  (fixed_of_lambdaBundle_objectCondition (LamObj.ofFrozen o) f La).symm

@[reducible] def LamLetters.toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : Formalism.L2.Pj.abelian₂.LamLetters o.toFrozen where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

@[reducible] def LamLetters.ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    LamLetters (LamObj.ofFrozen o) where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

theorem LamLetters.isLetter_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) (k : Fin o.xB.P.g)
    (w : epsR o.K₁ ⟶ o.xB.P.A) : L.toFrozen.IsLetter k w ↔ L.IsLetter k w := by
  unfold LamLetters.IsLetter Formalism.L2.Pj.abelian₂.LamLetters.IsLetter
  dsimp only
  cases L.src k <;> rfl

theorem LamLetters.isLetter_ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o)
    (k : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A) : (LamLetters.ofFrozen L).IsLetter k w ↔ L.IsLetter k w :=
  (LamLetters.isLetter_toFrozen (LamLetters.ofFrozen L) k w).symm

theorem LamLetters.isGood_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : L.toFrozen.IsGood ↔ L.IsGood := by
  unfold LamLetters.IsGood Formalism.L2.Pj.abelian₂.LamLetters.IsGood
  refine and_congr Iff.rfl (and_congr (forall_congr' fun b => forall_congr' fun i => ?_)
    (and_congr (forall_congr' fun k => exists_congr fun w => and_congr (L.isLetter_toFrozen k w) Iff.rfl)
      (forall_congr' fun k => ?_)))
  · dsimp only
    cases L.src (L.e ⟨b, i⟩) <;> rfl
  · dsimp only
    cases L.src k <;> rfl

theorem LamLetters.isGood_ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    (LamLetters.ofFrozen L).IsGood ↔ L.IsGood :=
  (LamLetters.isGood_toFrozen (LamLetters.ofFrozen L)).symm

omit [StarRing (𝓞 E)] in
theorem lambdaBundle_degree_iff (H : Host E) (x : ℝ) : LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x :=
  ⟨fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho),
   fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho)⟩

theorem lambdaBundle_index_iff : LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_length_iff : LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_conditions_iff :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ),
      GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧
    (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) :=
  ⟨fun _ _ _ _ H x => lambdaBundle_degree_iff H x, lambdaBundle_index_iff, lambdaBundle_length_iff⟩

end GlobalTheory.LamF
