import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntegralNormSqCoef

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core

open Formalism.QuantumDeterminants

section hpk

variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  have key : ∀ (c : ℕ) (hc : c < 2 * r + k + 1) (a : ℂ),
      ∑ j : Fin (2 * r + k + 1), (if j.val = c then a else 0) * v j = a * v ⟨c, hc⟩ := by
    intro c hc a
    rw [Finset.sum_eq_single ⟨c, hc⟩]
    · simp
    · intro b _ hb
      have hbc : b.val ≠ c := fun h => hb (Fin.ext h)
      simp [hbc]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [hpk_out k r h]
    rw [key _ (by omega), one_mul]
  · rw [if_neg h]
    simp only [hpk_mid k r h]
    rw [key i.val hi]
    split_ifs <;> simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h' : (2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := by omega
    rw [hpk_mulVec, if_pos h, hpk_mulVec, if_pos h']
    congr 1
    ext
    simp only
    omega
  · rw [hpk_mulVec, if_neg h, hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

end hpk

theorem inv_mul_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := hpk_sq k r

theorem mul_inv_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h := inv_mul_UH k r hg
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h)

theorem mul_mem_UH (k r : ℕ) {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem one_mem_UH (k r : ℕ) : (1 : Mat k r) ∈ UH (Hpk k r) := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem inv_mem_UH (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have e := mul_inv_UH k r hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e]; simp

theorem shift_mem_UH (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x₀ h m x : Mat k r)
    (hx₀ : x₀ ∈ UH (Hpk k r)) (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (hx : x ∈ UH (Hpk k r)) :
    x₀⁻¹ * (h * m * x) ∈ UH (Hpk k r) :=
  mul_mem_UH k r (inv_mem_UH k r x₀ hx₀) (mul_mem_UH k r (mul_mem_UH k r hh.1 hm.1) hx)

theorem coef_mul (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ)
    (y g : Mat k r) (hy : y ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    ⟪w, σ (y * g) w⟫_ℂ = ⟪σ y⁻¹ w, σ g w⟫_ℂ := by
  have hyi := inv_mem_UH k r y hy
  have hmul := hσ.1.2
  have h1 : σ y (σ y⁻¹ w) = w := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul y hy y⁻¹ hyi, mul_inv_UH k r hy, hσ.1.1]
    rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(σ y).toLinearMap, hσ.2.1 y hy⟩
  have hL := L.inner_map_map (σ y⁻¹ w) (σ g w)
  rw [hmul y hy g hg, ContinuousLinearMap.comp_apply]
  have e : ⟪w, σ y (σ g w)⟫_ℂ = ⟪σ y (σ y⁻¹ w), σ y (σ g w)⟫_ℂ := by rw [h1]
  rw [e]
  exact hL

theorem schur_shift (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ) (μG : Measure (Mt k r))
    (hσ : Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ) (hw : ‖w‖ = 1) (hF : IsFdegB μG σ d)
    (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG) (y : Mat k r) (hy : y ∈ UH (Hpk k r)) :
    Integrable (fun g : Mt k r => Formalism.MainNotions.S.eFun μG σ w (Matrix.of g) * ⟪w, σ (y * Matrix.of g) w⟫_ℂ) μG ∧
      ∫ g : Mt k r, Formalism.MainNotions.S.eFun μG σ w (Matrix.of g) * ⟪w, σ (y * Matrix.of g) w⟫_ℂ ∂μG = ⟪w, σ y w⟫_ℂ := by
  have hGae : ∀ᵐ g ∂μG, Matrix.of g ∈ UH (Hpk k r) := ae_iff.2 hG.2.2.1
  obtain ⟨hd, hS⟩ := hF
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnorm : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  have hsq : ∫ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
    have h1 := (hS w w w w).2
    have e : (fun g : Mt k r => ⟪w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ) =
        fun g => ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj']
      push_cast
      rfl
    rw [e, integral_complex_ofReal, hnorm] at h1
    apply Complex.ofReal_injective
    rw [h1]
    push_cast
    ring
  have hfd : Formalism.MainNotions.S.fdegH μG σ w = d := by
    unfold Formalism.MainNotions.S.fdegH
    rw [hsq, hw]
    field_simp
  have hpt : ∀ᵐ g ∂μG, Formalism.MainNotions.S.eFun μG σ w (Matrix.of g) * ⟪w, σ (y * Matrix.of g) w⟫_ℂ =
      (d : ℂ) * (⟪σ y⁻¹ w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ) :=
    hGae.mono fun g hg => by
      rw [coef_mul k r H σ w hσ y (Matrix.of g) hy hg]
      unfold Formalism.MainNotions.S.eFun
      rw [hfd]
      ring
  have hint := hS w (σ y⁻¹ w) w w
  refine ⟨(hint.1.const_mul (d : ℂ)).congr (hpt.mono fun g h => h.symm), ?_⟩
  rw [integral_congr_ae hpt, integral_const_mul, hint.2, hnorm]
  have hc := coef_mul k r H σ w hσ y 1 hy (one_mem_UH k r)
  rw [mul_one, hσ.1.1] at hc
  have hc' : ⟪σ y⁻¹ w, w⟫_ℂ = ⟪w, σ y w⟫_ℂ := by
    rw [hc]
    rfl
  rw [hc']
  field_simp

theorem repro_core : ReproCoreStatement := by
  unfold ReproCoreStatement
  intro k r H _ _ _ σ w d Vp _ _ _ ψ π z μG μW μN x₀ x ξ hσ hw hF hG hW hN hx₀ hx hI
  unfold Formalism.MainNotions.S.rconv sInt
  have := hG.1
  have := hW.1
  have := hN.1
  have hpW : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hW.2.2.1)
  have hpN : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hN.2.2.1)
  simp_rw [← integral_smul]
  rw [integral_integral_swap hI]
  refine integral_congr_ae ((hpW.and hpN).mono fun p hp => ?_)
  have hy := shift_mem_UH k r z x₀ (Matrix.of p.1) (Matrix.of p.2) x hx₀ hp.1 hp.2 hx
  simp_rw [smul_smul]
  rw [integral_smul_const]
  congr 1
  have e : ∀ g : Mt k r, x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * (x * Matrix.of g)) =
      x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x) * Matrix.of g := by
    intro g
    simp only [Matrix.mul_assoc]
  simp_rw [e]
  exact (schur_shift k r H σ w d μG hσ hw hF hG _ hy).2

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core
