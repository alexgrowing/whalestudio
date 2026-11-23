import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory.Sl2Ad

theorem form_ne_zero_of_isIrr : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ →
    ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  intro K _ _ Γ _ ρ hirr y hy hstab hform
  have hq : y 0 * y 1 + y 2 * y 2 = 0 := by
    rw [form_apply] at hform
    have h2 : (2 : K) * (y 0 * y 1 + y 2 * y 2) = 0 := by linear_combination hform
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hconj : ∀ g, ∃ c : K, ofCoord y * (ρ g : Matrix (Fin 2) (Fin 2) K) = (ρ g : Matrix (Fin 2) (Fin 2) K) * (c • ofCoord y) := by
    intro g
    obtain ⟨c, hc⟩ := hstab g⁻¹
    refine ⟨c, ?_⟩
    have h1 := coord_conj_ofCoord (ρ g⁻¹) y
    rw [hc] at h1
    have htr : ((ρ g⁻¹ : Matrix (Fin 2) (Fin 2) K) * ofCoord y * (((ρ g⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = 0 := by
      rw [trace_conj, trace_ofCoord]
    have h2 := ofCoord_coord htr
    rw [h1] at h2
    have h3 : ofCoord (c • y) = c • ofCoord y := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord]
    rw [h3, map_inv, inv_inv] at h2
    have hu : (ρ g : Matrix (Fin 2) (Fin 2) K) * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  let Wk : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (ofCoord y))
  have hmem : ∀ x, x ∈ Wk ↔ ofCoord y *ᵥ x = 0 := fun x => by
    simp [Wk, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hinv : IsInv ρ Wk := by
    intro g x hx
    rw [hmem] at hx ⊢
    obtain ⟨c, hc⟩ := hconj g
    have hs : (c • ofCoord y) *ᵥ x = c • (ofCoord y *ᵥ x) := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hs, hx, smul_zero, Matrix.mulVec_zero]
  have hy0 : ∀ a b c : K, a = 0 → b = 0 → c = 0 → y 0 = a → y 1 = b → y 2 = c → False := by
    intro a b c ha hb hc h0 h1 h2
    apply hy
    ext i; fin_cases i
    · simpa [ha] using h0
    · simpa [hb] using h1
    · simpa [hc] using h2
  rcases hirr.2.2 Wk le_top hinv with h | h
  · have hv1 : (![y 0, -y 2] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    have hv2 : (![y 2, y 1] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    rw [h, Submodule.mem_bot] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b1 := congrFun hv2 1
    simp at a0 a1 b1
    exact hy0 0 0 0 rfl rfl rfl a0 b1 a1
  · have hv1 : (Pi.single 0 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    have hv2 : (Pi.single 1 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    rw [hmem] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b0 := congrFun hv2 0
    simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0
    exact hy0 0 0 0 rfl rfl rfl b0 a1 a0

end GlobalTheory.Sl2Ad
