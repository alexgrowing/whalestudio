import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos

open CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private def cj (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![δ 0 0, -δ 0 1; -δ 1 0, δ 1 1], by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

private theorem eps_mul_cj (δ : SL(2, ℤ)) :
    eps * δ.1.map (Int.cast : ℤ → ℝ) = (cj δ).1.map (Int.cast : ℤ → ℝ) * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, cj, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_map (δ : SL(2, ℤ)) : (δ.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h := (Int.castRingHom ℝ).map_det δ.1
  rw [δ.det_coe, map_one] at h
  have h' : (δ.1.map (Int.cast : ℤ → ℝ)).det = 1 := h.symm
  rw [h']
  exact one_ne_zero

private theorem pos_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) : nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rw [← (nslMul k f).1 _ x (det_map δ) hx, (nslSl k f).1 δ, h, (nslMul k f).2.2.2]

private theorem gen_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) (h' : f ∣[(k : ℤ)] (cj δ) = c • f) :
    nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd : 0 < (eps * x).det := by
      rw [Matrix.det_mul]
      have : eps.det = -1 := by simp [eps]
      rw [this]
      linarith
    rw [← (nslMul k f).2.1, ← Matrix.mul_assoc, eps_mul_cj, Matrix.mul_assoc, pos_case k f _ hd _ c h',
      (nslMul k f).2.1]
  · exact pos_case k f x hpos δ c h

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslInv :
    UpperTheory.V.Af.Nf.NslInv := by
  intro k M f x hx
  refine ⟨fun hf δ hδ => ?_, fun χ hχ δ hδ => ?_⟩
  · have hδ' : cj δ ∈ Gamma1 M := by
      rw [Gamma1_mem] at hδ ⊢
      obtain ⟨h1, h2, h3⟩ := hδ
      refine ⟨?_, ?_, ?_⟩
      · exact h1
      · exact h2
      · show (((-δ 1 0 : ℤ)) : ZMod M) = 0
        rw [Int.cast_neg, h3, neg_zero]
    have := gen_case k f x hx δ 1 (by rw [one_smul]; exact hf δ hδ) (by rw [one_smul]; exact hf _ hδ')
    rwa [one_smul] at this
  · have hδ' : cj δ ∈ Gamma0 M := by
      rw [Gamma0_mem] at hδ ⊢
      show (((-δ 1 0 : ℤ)) : ZMod M) = 0
      rw [Int.cast_neg, hδ, neg_zero]
    exact gen_case k f x hx δ _ (hχ δ hδ) (hχ _ hδ')
