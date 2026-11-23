import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit

open Matrix

theorem vandermonde_integral_of_roots_of_unity : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ), ¬ p ∣ N → ∀ (w : Fin r → PadicAlgCl p), (∀ s, w s ^ N = 1) → Function.Injective w → ∀ (c : Fin r → PadicAlgCl p), (∀ s, ‖∑ j : Fin r, c j * w s ^ (j : ℕ)‖ ≤ 1) → ∀ j, ‖c j‖ ≤ 1 := by
  intro p _ N r hN w hw hinj c hc j
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero p)
  have hw1 : ∀ s, ‖w s‖ = 1 := fun s => by
    have h := congrArg norm (hw s)
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 h
  set S := Obar p
  let ws : Fin r → S := fun s => ⟨w s, mem_Obar_iff.2 (hw1 s).le⟩
  let ys : Fin r → S := fun s => ⟨∑ j : Fin r, c j * w s ^ (j : ℕ), mem_Obar_iff.2 (hc s)⟩
  let V' : Matrix (Fin r) (Fin r) S := Matrix.vandermonde ws
  have hmap : V'.map S.subtype = Matrix.vandermonde w := by
    ext s t; simp [V', ws, Matrix.vandermonde_apply]
  have hdet : ‖(Matrix.vandermonde w).det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    refine Finset.prod_eq_one fun k hk => ?_
    have hik : i < k := Finset.mem_Ioi.1 hk
    exact norm_sub_eq_one_of_pow_eq_one p hN (hw k) (hw i) (fun h => (ne_of_lt hik) (hinj h).symm)
  have hdetS : (S.subtype V'.det) = (Matrix.vandermonde w).det := by
    rw [RingHom.map_det, ← hmap]; rfl
  have hne : (Matrix.vandermonde w).det ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit V'.det := by
    have hmem : ((Matrix.vandermonde w).det)⁻¹ ∈ S := by
      rw [mem_Obar_iff, norm_inv, hdet, inv_one]
    refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ ?_
    apply Subtype.ext
    change S.subtype V'.det * _ = 1
    rw [hdetS, mul_inv_cancel₀ hne]
  let c' : Fin r → S := V'⁻¹ *ᵥ ys
  have hc' : V' *ᵥ c' = ys := by
    simp only [c', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hV : Matrix.vandermonde w *ᵥ (fun k => (c' k : PadicAlgCl p)) = Matrix.vandermonde w *ᵥ c := by
    funext s
    have h1 := RingHom.map_mulVec S.subtype V' c' s
    rw [hc', hmap] at h1
    change _ = (vandermonde w *ᵥ ⇑S.subtype ∘ c') s at h1
    rw [show (fun k => (c' k : PadicAlgCl p)) = ⇑S.subtype ∘ c' from rfl, ← h1]
    simp only [ys, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    simp [mul_comm]
  have hVu : IsUnit (Matrix.vandermonde w) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have hcc : (fun k => (c' k : PadicAlgCl p)) = c := by
    have := congrArg (fun v => (Matrix.vandermonde w)⁻¹ *ᵥ v) hV
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hVu), Matrix.one_mulVec] using this
  rw [← congrFun hcc j]
  exact mem_Obar_iff.1 (c' j).2

end GlobalTheory.LKRes.ResSplit
