import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.OmMorPullIndep

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.IterG

variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ κ' : O →+* b.R ⧸ b.I}

theorem gen_mu_nu {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {φb : b.R →+* b.R} (dφ : IsDPMorphism b.γ b.γ φb)
    (P : F.ptK κ ⟶ F.ptK κ) (str : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (φb r)))
    {σ₀ : Λ →+* Λ} (hc : ∀ a, φb (c a) = c (σ₀ a)) (N : ℕ) (d₁ : IsDPMorphism b.γ b.γ (RingHom.id b.R))
    (Pi : F.ptK κ ⟶ F.ptK κ') (si) (hi : ∀ a, RingHom.id b.R (c a) = c (RingHom.id Λ a)) (d₂ : IsDPMorphism b.γ b.γ (φb ^ N))
    (Po : F.ptK κ' ⟶ F.ptK κ) (so) (ho : ∀ a, (φb ^ N) (c a) = c ((σ₀ ^ N) a))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀), (Po.app B₀ (Pi.app B₀ y)).1.2 = ((PtN P N).app B₀ y).1.2)
    (j : ℕ) (x : CH.H (B.OM (F.cr b ht κ) c) j) :
    (B.omMor (c := c) (c' := c) (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (RingHom.id b.R) rfl d₁ Pi si) (RingHom.id Λ) hi).pull j
      ((B.omMor (c := c) (c' := c) (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (φb ^ N) rfl d₂ Po so) (σ₀ ^ N) ho).pull j x) =
      (⇑((B.omMor (c := c) (c' := c) (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) φb rfl dφ P str) σ₀ hc).pull j))^[N] x := by
  have h1 := comp_eq (ht := ht) c Pi d₁ si hi d₂ Po so (PtN P N) (strN P str N) ho hpt j x
  have h2 := iter_pull (ht := ht) c dφ P str hc j N x
  exact h1.trans h2.symm

end CrystallineSemistableComparison.IterG
