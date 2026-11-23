import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem genRank_le_sq (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) : genRank γ ≤ (q * Module.finrank ℚ E) ^ 2 := by
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have h1 : genRank γ ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) :=
    Submodule.finrank_le _
  have h2 : Module.finrank ℤ (LinearMap.BilinForm ℤ X) = Module.finrank ℤ X * Module.finrank ℤ X := by
    unfold LinearMap.BilinForm
    rw [Module.finrank_linearMap, Module.finrank_linearMap_self]
  have h3 : Module.finrank ℤ X ≤ q * Module.finrank ℚ E := by
    rw [finrank_int_eq_finrank_mul E X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  calc genRank γ ≤ Module.finrank ℤ X * Module.finrank ℤ X := h2 ▸ h1
    _ ≤ (q * Module.finrank ℚ E) * (q * Module.finrank ℚ E) := Nat.mul_le_mul h3 h3
    _ = (q * Module.finrank ℚ E) ^ 2 := (sq _).symm

theorem carrierDim_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro E _ _ _ H q ψ lab hlab
  refine ⟨(q * Module.finrank ℚ E) ^ 2, fun X _ _ _ _ hX β hβ hpos => ?_⟩
  rw [hlab X hX β hβ hpos]
  exact_mod_cast (by
    rcases Set.eq_empty_or_nonempty {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
        InRCone γ β ∧ genRank γ = k} with he | hne
    · rw [he, Nat.sInf_empty]; exact Nat.zero_le _
    · obtain ⟨m, γ, -, -, hk⟩ := Nat.sInf_mem hne
      rw [← hk]; exact genRank_le_sq E q X hX γ :
    sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ = k} ≤
      (q * Module.finrank ℚ E) ^ 2)

end GlobalTheory.PolFan
