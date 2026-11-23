import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW
import Formalism.FormalDegreeBessel.FinalG

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private def gAlast (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

private theorem gA_mulVec {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    Hpk k r *ᵥ v = fun i => Hpk k r i i * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hv j hj, mul_zero]
    · push Not at hj
      have hij : i ≠ j := fun h => hji h.symm
      have h0 : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hij h.2.2)]
      rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem gA_herm {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (Hpk k r i i * v i) := by
  simp only [herm, dotProduct, gA_mulVec hv, Pi.star_apply]

private theorem gA_term {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (i : Fin (2 * r + k + 1)) :
    star (x i) * (Hpk k r i i * x i) =
      ((Complex.normSq (x i) - 2 * (if i = gAlast k r then Complex.normSq (x i) else 0) : ℝ) : ℂ) := by
  by_cases hi : i.val < r ∨ r + k < i.val
  · simp [hx i hi]
  · push Not at hi
    have e : star (x i) * x i = (Complex.normSq (x i) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    have hH : Hpk k r i i = if i.val = r + k then -1 else 1 := by
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hi.1, hi.2, trivial⟩]
    rw [hH]
    by_cases hl : i = gAlast k r
    · have hv : i.val = r + k := by rw [hl]; rfl
      rw [if_pos hv, if_pos hl, show star (x i) * (-1 * x i) = -(star (x i) * x i) by ring, e]
      push_cast
      ring
    · have hv : i.val ≠ r + k := fun h => hl (Fin.ext h)
      rw [if_neg hv, if_neg hl, one_mul, e]
      simp

private theorem gA_self {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) :
    herm (Hpk k r) x x = ((∑ i, Complex.normSq (x i) - 2 * Complex.normSq (x (gAlast k r)) : ℝ) : ℂ) := by
  rw [gA_herm hx]
  simp_rw [gA_term hx]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp

private theorem gA_hz {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  have h : Tz k r z = -(herm (Hpk k r) z z).re := rfl
  rw [h, gA_self hz]
  simp

private theorem gA_smul_left (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem gA_smul_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H v (c • w) = star c * herm H v w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

private theorem gA_mul_star (c : ℂ) : c * star c = (Complex.normSq c : ℂ) := by rw [← starRingEnd_apply, Complex.mul_conj]

private theorem gA_normSq_star (c : ℂ) : Complex.normSq (star c) = Complex.normSq c := by rw [← starRingEnd_apply, Complex.normSq_conj]

private theorem gA_H_eI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Hpk, Fin.ext_iff, h1, h2]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem gA_H_esI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Hpk, Fin.ext_iff, h1, h2]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem gA_herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec j) = (Hpk k r *ᵥ v) j := by
  simp only [herm, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [bvec]
  · intro i _ hij
    simp [bvec, hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem gA_mv_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp [Matrix.mulVec, dotProduct, gA_H_eI]

private theorem gA_mv_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, gA_H_esI]

private theorem gA_inWb_iff (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r v ↔ ∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0 ∧
      herm (Hpk k r) v (bvec (esI k r a)) = 0 := by
  simp only [gA_herm_bvec, gA_mv_eI, gA_mv_esI]
  constructor
  · intro hv a
    have ha := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    exact ⟨hv _ (Or.inr (by omega)), hv _ (Or.inl (by omega))⟩
  · intro h i hi
    have hiv := i.isLt
    rcases hi with hi | hi
    · have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      have := (h ⟨i.val, hi⟩).2
      rwa [e] at this
    · have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i :=
        Fin.ext (show 2 * r + k - (2 * r + k - i.val) = i.val by omega)
      have := (h ⟨2 * r + k - i.val, by omega⟩).1
      rwa [e] at this

theorem glev_unit {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 := by
  obtain ⟨-, hHH, -, -⟩ := hpkFacts k r
  have hdet : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det hHH
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hu := ((uHGroup _ (Hpk k r) hdet).2.2 g hg.1).1
  exact ⟨Matrix.nonsing_inv_mul g hu, Matrix.mul_nonsing_inv g hu⟩

theorem glev_herm {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem glev_inWb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : inWb k r v) : inWb k r (g *ᵥ v) ∧ inWb k r (g⁻¹ *ᵥ v) := by
  have key : ∀ h ∈ Glev k r (Fin.last r), inWb k r (h *ᵥ v) := by
    intro h hh
    rw [gA_inWb_iff]
    intro a
    obtain ⟨h1, h2⟩ := hh.2 a a.isLt
    have hv' := (gA_inWb_iff v).1 hv a
    rw [← h1, ← h2, glev_herm hh, glev_herm hh]
    exact hv'
  obtain ⟨-, hHH, -, -⟩ := hpkFacts k r
  have hdet : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det hHH
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hl := (glev_unit hg).1
  have hinv : g⁻¹ ∈ Glev k r (Fin.last r) := by
    simp only [Glev, Set.mem_ofPred_eq]
    refine ⟨((uHGroup _ (Hpk k r) hdet).2.2 g hg.1).2, fun a ha => ?_⟩
    obtain ⟨h1, h2⟩ := hg.2 a ha
    constructor
    · calc g⁻¹ *ᵥ bvec (eI k r a) = g⁻¹ *ᵥ (g *ᵥ bvec (eI k r a)) := by rw [h1]
        _ = bvec (eI k r a) := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · calc g⁻¹ *ᵥ bvec (esI k r a) = g⁻¹ *ᵥ (g *ᵥ bvec (esI k r a)) := by rw [h2]
        _ = bvec (esI k r a) := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
  exact ⟨key g hg, key g⁻¹ hinv⟩

private theorem gA_fvec (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem not_prop_of_GG {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    (∀ c : ℂ, g⁻¹ *ᵥ z ≠ c • z') ∧ ∀ c : ℂ, g *ᵥ z' ≠ c • z := by
  constructor
  · intro c hc
    apply hGG
    have hz_eq : z = c • (g *ᵥ z') := by
      have h := congrArg (g *ᵥ ·) hc
      simp only [Matrix.mulVec_mulVec, (glev_unit hg).2, Matrix.one_mulVec, Matrix.mulVec_smul] at h
      exact h
    have hu : herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') = ((-Tz k r z' : ℝ) : ℂ) := by
      rw [glev_herm hg, gA_hz hz']
    have hzeta : zetaL k r z z' (Fin.last r) g = star c * ((-Tz k r z' : ℝ) : ℂ) := by
      simp only [zetaL, gA_fvec]
      rw [show herm (Hpk k r) (g *ᵥ z') z = herm (Hpk k r) (g *ᵥ z') (c • (g *ᵥ z')) by rw [← hz_eq],
        gA_smul_right, hu]
    have hT : Tz k r z = Complex.normSq c * Tz k r z' := by
      have h : Tz k r z = -(herm (Hpk k r) z z).re := rfl
      rw [h, hz_eq, gA_smul_left, gA_smul_right, ← mul_assoc, gA_mul_star, hu, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      ring
    simp only [GGl]
    rw [hzeta, hT, Complex.normSq_mul, gA_normSq_star, Complex.normSq_ofReal]
    ring
  · intro c hc
    apply hGG
    have hzeta : zetaL k r z z' (Fin.last r) g = c * ((-Tz k r z : ℝ) : ℂ) := by
      simp only [zetaL, gA_fvec]
      rw [hc, gA_smul_left, gA_hz hz]
    have hT : Tz k r z' = Complex.normSq c * Tz k r z := by
      have h1 : herm (Hpk k r) z' z' = herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') := (glev_herm hg z' z').symm
      rw [hc, gA_smul_left, gA_smul_right, ← mul_assoc, gA_mul_star, gA_hz hz] at h1
      have h : Tz k r z' = -(herm (Hpk k r) z' z').re := rfl
      rw [h, h1, ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    simp only [GGl]
    rw [hzeta, hT, Complex.normSq_mul, Complex.normSq_ofReal]
    ring

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
