import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x5

variable {k r : ℕ}

lemma herm_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : ι → ℂ)
    (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ c, x c • v c) w = ∑ c, x c * herm H (v c) w := by
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

lemma hzz_real (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
  have h := ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    simp only [Complex.ofReal_im]; linarith

lemma hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [hzz_real]; exact_mod_cast (neg_ne_zero.mpr hz.ne')

lemma herm_f_es {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    herm (Hpk k r) (fvec k r z c) (bvec (esI k r a)) = if c.val = a.val then 1 else 0 := by
  rw [bvec, ggHerm_bvec_right]
  have hlt : r + k < (esI k r a).val := by simp [esI]; omega
  rw [gn_Hpk_mulVec, dif_pos (Or.inr hlt)]
  have e : (⟨2 * r + k - (esI k r a).val, by omega⟩ : Fin (2 * r + k + 1)) = ⟨a.val, by omega⟩ := by
    apply Fin.ext; simp [esI]; omega
  rw [e, fvec_apply_lt z hz c _ (by simp)]

lemma herm_e_alt {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Fin (2 * r + k + 1))
    (hx : x.val < r ∨ r + k < x.val) : herm (Hpk k r) (bvec x) z = 0 := by
  rw [ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, ggHpk_mulVec_Wb k r z hz,
    hz x hx, mul_zero, star_zero]

lemma hermitian_form_flag_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c.val = r then herm (Hpk k r) z z else 0 := by
  unfold fvec
  split_ifs with h1 h2 h2
  · omega
  · exact herm_e_alt hz _ (Or.inl (by simp [eI, h1]))
  · rfl
  · omega

lemma uMap_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (s : B.Mat k r)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c) :
    C2.uMap k r z s = U := by
  ext a b
  unfold C2.uMap
  rw [h b]
  split_ifs with ha
  · rw [herm_sum_smul]
    simp only [herm_f_es hz.1]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; rw [if_neg (fun e => hc (Fin.ext e)), mul_zero]
    · simp
  · rw [herm_sum_smul]
    simp only [hermitian_form_flag_vector hz.1]
    rw [Finset.sum_eq_single a]
    · rw [if_pos (by have := a.isLt; omega)]
      field_simp [hzz_ne hz.2]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro e; apply hc; apply Fin.ext; have := a.isLt; omega
    · simp

lemma colEq {z : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : s * Fm k r z = Fm k r z * U) (b : Fin (r + 1)) :
    s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c := by
  funext i
  have := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Fm, Matrix.of_apply] at this
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

end C2x5

open C2x5

theorem unipotent_map_frame : C2.UMapFrame := by
  intro k r z hz
  refine ⟨fun s hs => ?_, fun h hh => ?_⟩
  · obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    have hu := uMap_eq hz s U (colEq hsF)
    refine ⟨by rw [hu]; exact colEq hsF, by rw [hu]; exact ⟨fun i j h => hU1 i j h, hU2⟩, fun t ht => ?_⟩
    obtain ⟨Ut, _, _, htF⟩ := S_F hz.1 ht
    have hut := uMap_eq hz t Ut (colEq htF)
    have hst : s * t * Fm k r z = Fm k r z * (U * Ut) := by
      rw [Matrix.mul_assoc, htF, ← Matrix.mul_assoc, hsF, Matrix.mul_assoc]
    rw [uMap_eq hz (s * t) (U * Ut) (colEq hst), hu, hut]
  · have h1 : h * Fm k r z = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
      rw [UW_F hh, Matrix.mul_one]
    exact uMap_eq hz h 1 (colEq h1)

theorem zhat_equivalence : C2.ZhatEquiv := by
  intro k r z z' hz hz' s hs s' hs' g
  obtain ⟨U, _, _, hsF⟩ := S_F hz.1 hs
  obtain ⟨U', _, _, hs'F⟩ := S_F hz'.1 hs'
  rw [uMap_eq hz s U (colEq hsF), uMap_eq hz' s' U' (colEq hs'F), Zhat_eq, Zhat_eq]
  have hsU : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hu : IsUnit s.det := WeylGroupFacts.isUnit_of_uh hsU
  have hHs : Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
    calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hsU]
      _ = sᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc (Fm k r z)ᴴ * Hpk k r * (s⁻¹ * g * s') * Fm k r z'
      = (Fm k r z)ᴴ * (Hpk k r * s⁻¹) * g * (s' * Fm k r z') := by simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r) * g * (Fm k r z' * U') := by rw [hHs, hs'F]
    _ = (s * Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Fm k r z * U)ᴴ * Hpk k r * g * Fm k r z' * U' := by rw [hsF]
    _ = Uᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z') * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P
