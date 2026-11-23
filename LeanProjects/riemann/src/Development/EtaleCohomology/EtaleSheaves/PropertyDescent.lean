import Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafPropsDescendPf

def LeafSpreadOne : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsProper c →
    SmoothOfRelativeDimension 1 c → IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsProper q' ∧ SmoothOfRelativeDimension 1 q'

def LeafBaseChangePre : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR)

theorem LeafPropsDescend_of (hS : LeafSpreadOne) (hB : LeafBaseChangePre) : LeafPropsDescend := by
  intro k _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 hc0 h1 h2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨f0, f1, f2, p0, p1, p2, -, -⟩ := id hpre
  obtain ⟨S0, hS0, fS0, H0⟩ := hS k Ω R hR c0 q v0 f0 hc0.2.1 hc0.2.2 p0
  obtain ⟨S1, hS1, quaternionDoubleCosetIndicator, H1⟩ := hS k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1 h1.2.2 p1
  obtain ⟨S2, hS2, fS2, H2⟩ := hS k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1 h2.2.2 p2
  have l0 : S0 ≤ S0 ⊔ S1 ⊔ S2 := le_sup_left.trans le_sup_left
  have l1 : S1 ≤ S0 ⊔ S1 ⊔ S2 := le_sup_right.trans le_sup_left
  have l2 : S2 ≤ S0 ⊔ S1 ⊔ S2 := le_sup_right
  have hRR : R ≤ S0 ⊔ S1 ⊔ S2 := hS0.trans l0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2⟩ :=
    hB k Ω R _ hRR c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨pr0, sm0⟩ := H0 _ l0 hRR E0 q' r0 Q0
  obtain ⟨pr1, sm1⟩ := H1 _ l1 hRR E1 (e1 ≫ q') r1 Q1
  obtain ⟨pr2, sm2⟩ := H2 _ l2 hRR E2 (e2 ≫ e1 ≫ q') r2 Q2
  exact ⟨_, (fS0.sup quaternionDoubleCosetIndicator).sup fS2, E0, E1, E2, q', e1, e2, w0, w1, w2,
    pr0, sm0, pr1, sm1, pr2, sm2, P0, P1, P2, c1, c2⟩

end LateralTheory.E.LeafPropsDescendPf

end
