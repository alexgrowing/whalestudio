import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
import Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
import Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.QuasiFiniteDescent

def QFChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (R : Subalgebra k Ω)
    {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) : Prop :=
  IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
  IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧
  γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafQFOmega : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) ∧ LocallyQuasiFinite γ1 ∧ LocallyQuasiFinite γ2

def LeafDescendPreMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 ∧ v0 ≫ f = e

def LeafSpreadQF : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) → LocallyQuasiFinite γ1 → LocallyQuasiFinite γ2 →
    ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 → v0 ≫ f = e →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (f' : E0 ⟶ X) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2)
      (hf' : f' ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
      QFChain p R' c0 γ1 γ2 e q' e1 e2 f' w0 w1 w2 hf'

def LeafReducedSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), SmoothOfRelativeDimension 1 q → AlgebraicGeometry.IsReduced D

theorem integral_of (hI : LeafIrred) (hR : LeafReducedSmooth) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k Ω) (hFG : R.FG) {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D)
    (hc : IsCurve c) (hs : SmoothOfRelativeDimension 1 q) (hp : IsPullback v c q (toR R)) : IsIntegral D := by
  have := hI k Ω R hFG c q v hc hs hp
  have := hR k Ω R hFG q hs
  exact isIntegral_of_irreducibleSpace_of_isReduced D

theorem goal_of (hQ : LeafQFOmega) (hP : LeafDescendPreMap) (hS : LeafSpreadQF) (hI : LeafIrred)
    (hR : LeafReducedSmooth) (hD : LeafDimBound) : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨q0, q1, q2⟩ := hQ k p Ω hdim c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hFG, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, hpre, hve⟩ :=
    hP k p Ω c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', hc⟩ :=
    hS k p Ω R hFG c0 γ1 γ2 e he hc0 h1 h2 q0 q1 q2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, l0, l1, l2, P0, P1, P2, m1, m2, m3⟩ := hc
  exact ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', a1, a2, a3, b1, b2, b3, c1, c2, c3,
    integral_of hI hR R' hFG' c0 q' w0 hc0 a3 P0, integral_of hI hR R' hFG' (γ1 ≫ c0) (e1 ≫ q') w1 h1 b3 P1,
    integral_of hI hR R' hFG' (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') w2 h2 c3 P2, l0, l1, l2,
    hD k Ω R' hFG' q' a3, P0, P1, P2, m1, m2, m3⟩

end LateralTheory.E.QuasiFiniteDescent

end
