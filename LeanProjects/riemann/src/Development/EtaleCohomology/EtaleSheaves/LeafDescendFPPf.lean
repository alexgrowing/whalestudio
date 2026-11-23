import Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafDescendFPPf

def FP {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

theorem fp_of_curve {Ω : Type} [Field Ω] {C : Scheme.{0}} {c : C ⟶ Sp Ω} (h : IsCurve c) : FP c := by
  obtain ⟨_, hp, hs⟩ := h
  have := hp
  have := hs
  refine ⟨inferInstance, inferInstance, inferInstance⟩

def LeafObjFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
      FP q ∧ IsPullback v f q (toR R)

def LeafPairFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → IsPullback v0 c0 q (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

def LeafTripleFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), FP (γ2 ≫ γ1 ≫ c0) →
    ∀ {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP (d1 ≫ q) →
    IsPullback v0 c0 q (toR R) → IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) → γ1 ≫ v0 = v1 ≫ d1 →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2), PreChain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2

theorem diagramDescent_of_objects_pairs_triples (hO : LeafObjFP) (hP : LeafPairFP) (hT : LeafTripleFP) : LeafDescendFP := by
  intro k _ Ω _ _ C0 c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, q, v0, hq, hsq⟩ := hO k Ω c0 (fp_of_curve hc0)
  obtain ⟨R', hR', E0, E1, q', e1, w0, w1, hq', he1, hs0, hs1, hc⟩ :=
    hP k Ω R hR c0 γ1 (fp_of_curve h1) q v0 hq hsq
  exact hT k Ω R' hR' c0 γ1 γ2 (fp_of_curve h2) q' e1 w0 w1 hq' he1 hs0 hs1 hc

end LateralTheory.E.LeafDescendFPPf

end
