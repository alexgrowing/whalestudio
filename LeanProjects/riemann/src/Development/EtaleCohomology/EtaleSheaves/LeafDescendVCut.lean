import Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafDescendVCut

abbrev toR {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) : Sp Ω ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

abbrev incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

def Chain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendChain : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2

def LeafDescendMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0), IsProper q → IsPullback v0 c0 q (toR R) → ∀ (e : C0 ⟶ X),
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∃ (R' : Subalgebra k Ω) (hR : R ≤ R'), R'.FG ∧ ∀ (E0 : Scheme.{0}) (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0)
      (w0 : C0 ⟶ E0), IsPullback r q' q (incl hR) → IsPullback w0 c0 q' (toR R') → w0 ≫ r = v0 →
      ∃ f : E0 ⟶ X, w0 ≫ f = e ∧ f ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))

def LeafBaseChange : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r : E0 ⟶ D0), Chain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2 ∧ IsPullback r q' q (incl hR) ∧
      w0 ≫ r = v0

def LeafIrred : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), IsCurve c0 →
    SmoothOfRelativeDimension 1 q → IsPullback v0 c0 q (toR R) → IrreducibleSpace D0

def LeafDimBound : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R), SmoothOfRelativeDimension 1 q →
    topologicalKrullDim D0 ≤ ringKrullDim R + 1

theorem goal_of (hA : LeafDescendChain) (hB : LeafDescendMap) (hC : LeafBaseChange) (hI : LeafIrred)
    (hD : LeafDimBound) : LateralTheory.E.LeafSpreadVCut.LeafDescendV := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, v0, v1, v2, hch⟩ := hA k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hRR', hR', hM⟩ := hB k p Ω R hR c0 q v0 hch.1 hch.2.2.2.2.2.2.1 e he
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r, hch', hr, hw⟩ :=
    hC k Ω R R' hRR' c0 γ1 γ2 q d1 d2 v0 v1 v2 hch
  obtain ⟨f, hf1, hf2⟩ := hM E0 q' r w0 hr hch'.2.2.2.2.2.2.1 hw
  obtain ⟨pq, sq, pq1, sq1, pq2, sq2, P0, P1, P2, c1, c2⟩ := hch'
  exact ⟨R', hR', E0, E1, E2, q', e1, e2, f, w0, w1, w2, pq, sq, pq1, sq1, pq2, sq2, hf2,
    hI k Ω R' hR' c0 q' w0 hc0 sq P0, hD k Ω R' hR' q' sq, P0, P1, P2, c1, c2, hf1⟩

end LateralTheory.E.LeafDescendVCut

end
