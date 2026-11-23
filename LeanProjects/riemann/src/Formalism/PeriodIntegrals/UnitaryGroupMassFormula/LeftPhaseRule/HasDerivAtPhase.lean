import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.MulApplyS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.ReflectionColumnDualIsotropic

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

lemma hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)

lemma hH2 (X : Mx k r) : Hpk k r * (Hpk k r * X) = X := by
  rw [← mul_assoc, Formalism.QuantumDeterminants.GBasic.Hpk_sq k r, one_mul]

lemma uh_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [mul_assoc]
    _ = 1 := by rw [hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq k r]

lemma dag_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    g * (Hpk k r * Zᴴ * Hpk k r) * g⁻¹ = Hpk k r * (g * Z * g⁻¹)ᴴ * Hpk k r := by
  rw [uh_inv_eq hg]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc, hH2]

lemma hpart1_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    g * hpart1 (Hpk k r) Z * g⁻¹ = hpart1 (Hpk k r) (g * Z * g⁻¹) := by
  simp only [hpart1, hinv]
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, dag_conj hg]

lemma hpart2_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    g * hpart2 (Hpk k r) Z * g⁻¹ = hpart2 (Hpk k r) (g * Z * g⁻¹) := by
  simp only [hpart2, hinv]
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, dag_conj hg]

lemma dagdag (M : Mx k r) : Hpk k r * (Hpk k r * Mᴴ * Hpk k r)ᴴ * Hpk k r = M := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc, hH2,
    Formalism.QuantumDeterminants.GBasic.Hpk_sq, mul_one]

lemma hpart1_skew (Z : Mx k r) :
    Hpk k r * (hpart1 (Hpk k r) Z)ᴴ * Hpk k r = -hpart1 (Hpk k r) Z := by
  simp only [hpart1, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, dagdag]
  ext i j
  simp
  ring

lemma hpart2_skew (Z : Mx k r) :
    Hpk k r * (hpart2 (Hpk k r) Z)ᴴ * Hpk k r = -hpart2 (Hpk k r) Z := by
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg,
      one_div_neg_eq_neg_one_div]
  simp only [hpart2, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, dagdag, hc]
  rw [neg_smul, add_comm (Hpk k r * Zᴴ * Hpk k r) Z]

lemma exp_uh {Y : Mx k r} (hY : Hpk k r * Yᴴ * Hpk k r = -Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ UH (Hpk k r) := by
  have hH := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hU : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, hH, hH⟩, rfl⟩
  have hY' : Yᴴ = Hpk k r * -Y * Hpk k r := by
    rw [← hY]
    simp only [← mul_assoc, hH, one_mul]
    rw [mul_assoc, hH, mul_one]
  have hYH : ((t : ℂ) • Y)ᴴ = Hpk k r * -((t : ℂ) • Y) * (Hpk k r)⁻¹ := by
    rw [hinv, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hY']
    simp only [smul_neg, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • Y))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • Y) = Hpk k r
  rw [← Matrix.exp_conjTranspose, hYH, Matrix.exp_conj _ _ hU, hinv]
  simp only [mul_assoc]
  rw [← mul_assoc (Hpk k r) (Hpk k r), hH, one_mul,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • Y))), neg_add_cancel,
    NormedSpace.exp_zero, mul_one]

lemma dag_apply (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Mᴴ * Hpk k r) p q =
      WeylGroupFacts.sgn k r p * (star (M (tau k r q) (tau k r p)) * WeylGroupFacts.sgn k r q) := by
  have hs : ∀ i, star (WeylGroupFacts.sgn k r i) = WeylGroupFacts.sgn k r i := by
    intro i; unfold WeylGroupFacts.sgn; split_ifs <;> simp
  have e : Mᴴ * Hpk k r = (Hpk k r * M)ᴴ := by
    rw [Matrix.conjTranspose_mul, Formalism.QuantumDeterminants.GBasic.Hpk_herm]
  rw [mul_assoc, hpk_mul_apply, e, Matrix.conjTranspose_apply, hpk_mul_apply, star_mul', hs]
  ring

lemma inS_dag {l : Fin r} {M : Mx k r} (hM : InS k r l M) : InS k r l (Hpk k r * Mᴴ * Hpk k r) := by
  unfold InS at hM ⊢
  intro p q hpq
  rw [dag_apply, hM (tau k r q) (tau k r p) ?_, star_zero, zero_mul, mul_zero]
  intro h
  apply hpq
  unfold SP at h ⊢
  simp only [tau, Fin.val_mk] at h
  have hl := l.isLt
  have hp := p.isLt
  have hq := q.isLt
  split_ifs at h <;> omega

lemma hasDerivAt_phase (A B : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (((cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B)).re : ℝ) : ℂ)))
      (Complex.I * (((cStd * A).re : ℝ) : ℂ)) 0 := by
  have e : ∀ t : ℝ, (cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B)).re = t * (cStd * A).re + t ^ 2 * (cStd * B).re := by
    intro t
    have h : cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B) = (t : ℂ) * (cStd * A) + ((t ^ 2 : ℝ) : ℂ) * (cStd * B) := by
      push_cast; ring
    rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp_rw [e]
  have ha : HasDerivAt (fun t : ℝ => t * (cStd * A).re) (1 * (cStd * A).re) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul_const _
  have hb : HasDerivAt (fun t : ℝ => t ^ 2 * (cStd * B).re) (((2 : ℕ) : ℝ) * (0 : ℝ) ^ (2 - 1) * (cStd * B).re) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  have h1 : HasDerivAt (fun t : ℝ => t * (cStd * A).re + t ^ 2 * (cStd * B).re) ((cStd * A).re) 0 :=
    (ha.add hb).congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul Complex.I).cexp
  exact h2.congr_deriv (by simp)

lemma rdV_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (X : Mx k r) (hS : InS k r l (g * X * g⁻¹))
    (hk : Hpk k r * (g * X * g⁻¹)ᴴ * Hpk k r = -(g * X * g⁻¹)) :
    RdV X f g = (Complex.I * (((cStd * ell k r z (g * X * g⁻¹)).re : ℝ) : ℂ)) • f g := by
  have ell_sm : ∀ (c : ℂ) (M : Mx k r), ell k r z (c • M) = c * ell k r z M := by
    intro c M
    simp only [ell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨hgG, hgD⟩ := hg
  have hgU : g ∈ UH (Hpk k r) := by
    have h := hgG
    simp only [Glev, Set.mem_setOf_eq] at h
    exact h.1
  have hleft : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hgU
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [mul_assoc]
      _ = 1 := by rw [hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq k r]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hdet
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  set Y := g * X * g⁻¹ with hYdef
  have hconj : ∀ u : ℝ, g * NormedSpace.exp ((u : ℂ) • X) = NormedSpace.exp ((u : ℂ) • Y) * g := by
    intro u
    have h1 : (u : ℂ) • Y = g * ((u : ℂ) • X) * g⁻¹ := by
      rw [hYdef, mul_smul_comm, smul_mul_assoc]
    rw [h1, Matrix.exp_conj _ _ hU, mul_assoc, hgi, mul_one]
  have hSu : ∀ u : ℝ, InS k r l ((u : ℂ) • Y) := fun u => inS_smul _ hS
  have hmemN : ∀ u : ℝ, NormedSpace.exp ((u : ℂ) • Y) ∈ Nlev k r l.castSucc := by
    intro u
    have hUu := exp_uh hk u
    rw [exp_S (hSu u)] at hUu ⊢
    exact memN_S (hSu u) hUu
  have hfe : ∀ u : ℝ, f (g * NormedSpace.exp ((u : ℂ) • X)) =
      psi k r z cStd (NormedSpace.exp ((u : ℂ) • Y)) • f g := by
    intro u
    rw [hconj u]
    exact hL g ⟨hgG, hgD⟩ _ (hmemN u)
  have hell : ∀ u : ℝ, ell k r z (NormedSpace.exp ((u : ℂ) • Y)) =
      (u : ℂ) * ell k r z Y + (u : ℂ) ^ 2 * ((1 / 2 : ℂ) * ell k r z (Y * Y)) := by
    intro u
    rw [exp_S (hSu u), ell_add, ell_add, ell_one z hz]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ell_sm]
    ring
  have hfun : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =
      fun u : ℝ => Complex.exp (Complex.I * (((cStd * ((u : ℂ) * ell k r z Y +
        (u : ℂ) ^ 2 * ((1 / 2 : ℂ) * ell k r z (Y * Y)))).re : ℝ) : ℂ)) • f g := by
    funext u
    rw [hfe u, ← hell u]
    rfl
  have hd := (hasDerivAt_phase (ell k r z Y) ((1 / 2 : ℂ) * ell k r z (Y * Y))).smul_const (f g)
  show deriv (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0 = _
  rw [hfun]
  exact hd.deriv

lemma phase_sum (A B : ℂ) :
    Complex.I * (((cStd * ((1 / 2 : ℂ) * (A - B))).re : ℝ) : ℂ) +
      Complex.I * (Complex.I * (((cStd * ((1 / (2 * Complex.I) : ℂ) * (A + B))).re : ℝ) : ℂ)) = A + star B := by
  have h1 : cStd * ((1 / 2 : ℂ) * (A - B)) = -Complex.I * (A - B) := by
    simp only [cStd]; ring
  have h2 : cStd * ((1 / (2 * Complex.I) : ℂ) * (A + B)) = -(A + B) := by
    simp only [cStd]; field_simp
  rw [h1, h2]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (a b : Fin (2 * r + k + 1))
    (hS : InS k r l (g * Matrix.single a b 1 * g⁻¹)) :
    EH k r a b f g = (ell k r z (g * Matrix.single a b 1 * g⁻¹) +
      star (ell k r z (Hpk k r * (g * Matrix.single a b 1 * g⁻¹)ᴴ * Hpk k r))) • f g := by
  have ell_sm : ∀ (c : ℂ) (M : Mx k r), ell k r z (c • M) = c * ell k r z M := by
    intro c M
    simp only [ell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  set W := g * Matrix.single a b 1 * g⁻¹ with hW
  have hgU : g ∈ UH (Hpk k r) := by
    have h := hg.1
    simp only [Glev, Set.mem_setOf_eq] at h
    exact h.1
  have hp1 : hpart1 (Hpk k r) W = (1 / 2 : ℂ) • (W - Hpk k r * Wᴴ * Hpk k r) := by
    simp only [hpart1, hinv]
  have hp2 : hpart2 (Hpk k r) W = (1 / (2 * Complex.I) : ℂ) • (W + Hpk k r * Wᴴ * Hpk k r) := by
    simp only [hpart2, hinv]
  have hS1 : InS k r l (g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart1_conj hgU, ← hW, hp1]
    exact inS_smul _ (inS_sub hS (inS_dag hS))
  have hS2 : InS k r l (g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart2_conj hgU, ← hW, hp2]
    exact inS_smul _ (inS_add hS (inS_dag hS))
  have hk1 : Hpk k r * (g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹)ᴴ * Hpk k r =
      -(g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart1_conj hgU]; exact hpart1_skew _
  have hk2 : Hpk k r * (g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹)ᴴ * Hpk k r =
      -(g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart2_conj hgU]; exact hpart2_skew _
  have r1 := rdV_left hz hL hg _ hS1 hk1
  have r2 := rdV_left hz hL hg _ hS2 hk2
  rw [hpart1_conj hgU, ← hW] at r1
  rw [hpart2_conj hgU, ← hW] at r2
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f g +
    Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f g = _
  rw [r1, r2, smul_smul, ← add_smul, hp1, hp2, ell_sm, ell_sm]
  congr 1
  have hsub : ell k r z (W - Hpk k r * Wᴴ * Hpk k r) = ell k r z W - ell k r z (Hpk k r * Wᴴ * Hpk k r) := by
    rw [sub_eq_add_neg, ell_add, ← neg_one_smul ℂ (Hpk k r * Wᴴ * Hpk k r), ell_sm]; ring
  rw [hsub, ell_add]
  exact phase_sum _ _

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
