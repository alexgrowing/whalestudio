import Formalism.FrobeniusContraction.Statement

noncomputable section

namespace Formalism.WachCohomologyFacts.PCoh

open Formalism.WachCohomologyFacts

section One

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
  [IsScalarTower O AA V] (W : WachDatum E n V)

theorem Φ_apply (x : ZMod n → V) (j : ZMod n) : W.Φ x j = W.φ (j - 1) (x (j - 1)) := rfl

theorem Γ_apply (x : ZMod n → V) (j : ZMod n) : W.Γ x j = W.γ j (x j) := rfl

theorem ΓΦ_comm (x : ZMod n → V) : W.Γ (W.Φ x) = W.Φ (W.Γ x) := by
  funext j
  rw [Γ_apply, Φ_apply, Φ_apply, Γ_apply, W.comm (j - 1) (x (j - 1)), sub_add_cancel]

end One

section Two

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]
  {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)

theorem fD_apply (x : ZMod n → V₁) (j : ZMod n) : h.fD x j = h.f (x j) := rfl

theorem fD_Φ (x : ZMod n → V₁) : h.fD (W₁.Φ x) = W₂.Φ (h.fD x) := by
  funext j
  simp only [fD_apply, Φ_apply, h.φ_comm]

theorem fD_Γ (x : ZMod n → V₁) : h.fD (W₁.Γ x) = W₂.Γ (h.fD x) := by
  funext j
  simp only [fD_apply, Γ_apply, h.γ_comm]

end Two

end Formalism.WachCohomologyFacts.PCoh
