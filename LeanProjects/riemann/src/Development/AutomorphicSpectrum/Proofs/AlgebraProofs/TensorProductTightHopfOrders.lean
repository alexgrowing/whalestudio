import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.ReTens

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), (∀ x : N₁, p • x = 0) → (∀ x : N₂, p • x = 0) → IsTight v p A₁.carrier → IsTight v p A₂.carrier → IsTight v p (tens A₁.carrier A₂.carrier) := by
  intro p _ C _ _ _ v R _ _ hv hp N₁ _ _ _ N₂ _ _ _ A₁ A₂ _ _ h1 h2
  unfold IsTight at h1 h2 ⊢
  obtain ⟨a1, c1, o1, hA1, hC1, hO1, e1, f1⟩ := h1
  obtain ⟨a2, c2, o2, hA2, hC2, hO2, e2, f2⟩ := h2
  obtain ⟨AA, hAA, hl, hr, s1, s2, hcol⟩ := PositivityTheory.HtPt.Re.tens_hopf p C v R hv hp N₁ N₂ A₁ A₂
  rw [← hAA]
  have st1 : ∀ g ∈ AA.carrier, (fun x : N₁ × N₂ =>
      g ((AddMonoidHom.inl N₁ N₂) ((AddMonoidHom.fst N₁ N₂) x))) ∈ AA.carrier := by
    intro g hg
    simpa using s1 g hg
  have st2 : ∀ g ∈ AA.carrier, (fun x : N₁ × N₂ =>
      g ((AddMonoidHom.inr N₁ N₂) ((AddMonoidHom.snd N₁ N₂) x))) ∈ AA.carrier := by
    intro g hg
    simpa using s2 g hg
  have hAF := PositivityTheory.HtPt.Re.ret_af p C v R hv hp (N₁ × N₂) AA N₁ N₂ (AddMonoidHom.inl N₁ N₂)
    (AddMonoidHom.fst N₁ N₂) (AddMonoidHom.inr N₁ N₂) (AddMonoidHom.snd N₁ N₂)
    (fun y => by simp) (fun y => by simp) (fun x => by simp) (fun y => by simp) (fun y => by simp)
    st1 st2 a1 a2 (by rw [hl]; exact hA1) (by rw [hr]; exact hA2)
  have hOm := PositivityTheory.HtPt.Re.ret_om hv AA (AddMonoidHom.inl N₁ N₂)
    (AddMonoidHom.fst N₁ N₂) (AddMonoidHom.inr N₁ N₂) (AddMonoidHom.snd N₁ N₂)
    (fun y => by simp) (fun y => by simp) (fun x => by simp) (fun y => by simp) (fun y => by simp)
    st1 st2 o1 o2 (by rw [hl]; exact hO1) (by rw [hr]; exact hO2)
  refine ⟨a1 * a2, c1 ^ Fintype.card N₂ * c2 ^ Fintype.card N₁, o1 * o2, hAF, hcol c1 c2 hC1 hC2, hOm, ?_, ?_⟩
  · rw [Fintype.card_prod, mul_pow]
    have k1 : a1 ^ (Fintype.card N₁ * Fintype.card N₂ * (p - 1)) =
        (a1 ^ (Fintype.card N₁ * (p - 1))) ^ Fintype.card N₂ := by
      rw [← pow_mul]
      congr 1
      ring
    have k2 : a2 ^ (Fintype.card N₁ * Fintype.card N₂ * (p - 1)) =
        (a2 ^ (Fintype.card N₂ * (p - 1))) ^ Fintype.card N₁ := by
      rw [← pow_mul]
      congr 1
      ring
    rw [k1, k2, e1, e2]
    ring
  · rw [Fintype.card_prod, mul_pow]
    have k1 : o1 ^ (Fintype.card N₁ * Fintype.card N₂) = (o1 ^ Fintype.card N₁) ^ Fintype.card N₂ :=
      pow_mul _ _ _
    have k2 : o2 ^ (Fintype.card N₁ * Fintype.card N₂) = (o2 ^ Fintype.card N₂) ^ Fintype.card N₁ := by
      rw [← pow_mul, _root_.mul_comm (Fintype.card N₂)]
    rw [k1, k2, f1, f2]
    ring
