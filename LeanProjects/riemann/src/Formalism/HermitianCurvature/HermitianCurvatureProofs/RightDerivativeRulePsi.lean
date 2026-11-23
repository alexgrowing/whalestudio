import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem first_expansion_of_parts : ExpansionFirstCaseFromComponents := by
  unfold ExpansionFirstCaseFromComponents
  intros
  exact first_expansion_identity
theorem second_expansion_of_parts : ExpansionSecondCaseFromComponents := by
  unfold ExpansionSecondCaseFromComponents
  intros
  exact second_expansion_identity
theorem third_expansion_of_parts : ExpansionThirdCaseFromComponents := by
  unfold ExpansionThirdCaseFromComponents
  intros
  exact column_indicator_expansion
theorem fourth_expansion_of_parts : ExpansionFourthCaseFromComponents := by
  unfold ExpansionFourthCaseFromComponents
  intros
  exact fourth_expansion_identity
theorem chain_first_of_parts : LastColumnChainFromComponents := by
  unfold LastColumnChainFromComponents
  intros
  exact chain_first_identity

theorem herm_bvec_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    herm H (bvec p) (bvec q) = H q p := by
  have hs : star (bvec q) = bvec q := by
    ext i
    by_cases h : i = q <;> simp [bvec, Pi.single_apply, h]
  unfold herm
  rw [hs]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

section dp
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))

theorem dp1 (hp : p.val < r) (hq : q.val < r) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_pos ⟨hp, hq⟩]
theorem dp2 (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    dpsiP k r z' p q = if p.val + 1 = r then z' q else 0 := by
  rw [dpsiP, if_neg (by omega), if_pos ⟨hp, hq1, hq2⟩]
theorem dp0 (hp : p.val < r) (hq : r + k < q.val) : dpsiP k r z' p q = 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem dp3 (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    dpsiP k r z' p q = if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_pos ⟨hp1, hp2, hq⟩]
theorem dp4 (hp : r + k < p.val) (hq : r + k < q.val) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hp, hq⟩]
end dp

theorem hpk_row_eI {k r : ℕ} (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) p = if p.val = 2 * r + k - b.val then 1 else 0 := by
  have hb := b.isLt
  have heI : (eI k r b).val = b.val := rfl
  simp only [Hpk]
  by_cases h : p.val = 2 * r + k - b.val
  · rw [if_pos h, if_pos ⟨by rw [heI]; exact hb, by rw [heI]; omega⟩]
  · rw [if_neg h, if_neg (fun hc => h (by rw [heI] at hc; omega)),
      if_neg (fun hc => by rw [heI] at hc; omega),
      if_neg (fun hc => by rw [heI] at hc; exact absurd hc.1 (by omega))]

theorem right_derivative_rule_psi : RuleRightDpsi := by
  intro k r z' l j hw
  have hl := l.isLt
  have hj := j.isLt
  simp only [Formalism.FourierDecayAlt.Q.mdim, Fin.val_succ] at hj
  have heI : ∀ a : Fin r, (eI k r a).val = a.val := fun _ => rfl
  have hesI : ∀ a : Fin r, (esI k r a).val = 2 * r + k - a.val := fun _ => rfl
  have hqv : (Formalism.FourierDecayAlt.Q.posL k r l.succ j).val = j.val + l.val + 1 := by
    simp only [Formalism.FourierDecayAlt.Q.posL, Fin.val_succ]
    omega
  have hz : ∀ q : Fin (2 * r + k + 1), (q.val < r ∨ r + k < q.val) →
      herm (Hpk k r) (bvec q) z' = 0 := by
    intro q hq
    unfold herm
    show ∑ m, (star z') m * (Hpk k r *ᵥ bvec q) m = 0
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : r ≤ m.val ∧ m.val ≤ r + k
    · have h0 : (Hpk k r *ᵥ bvec q) m = 0 := by
        have e : (Hpk k r *ᵥ bvec q) m = Hpk k r m q := by
          simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
        rw [e]
        simp only [Hpk]
        rw [if_neg (fun hc => by omega), if_neg (fun hc => by omega),
          if_neg (fun hc => by rw [hc.2.2] at hm; omega)]
      rw [h0, mul_zero]
    · have h0 : z' m = 0 := hw m (by omega)
      simp [h0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold InNp
    rw [heI, hqv]
    omega
  · by_cases hlr : l.val + 1 < r
    · have hf : fvec k r z' l.succ = bvec (eI k r ⟨l.val + 1, hlr⟩) := by
        simp only [fvec, Fin.val_succ, dif_pos hlr]
      have hv : (eI k r (⟨l.val + 1, hlr⟩ : Fin r)).val = l.val + 1 := rfl
      simp only [Formalism.FourierDecayAlt.Q.xv, hf, bvec, Pi.single_apply, Fin.ext_iff, hv, hqv, dpsiP, heI]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hf : fvec k r z' l.succ = z' := by
        simp only [fvec, Fin.val_succ, dif_neg hlr]
      simp only [Formalism.FourierDecayAlt.Q.xv, hf, dpsiP, heI, hqv]
      split_ifs <;> first
        | rfl
        | (exfalso; omega)
        | exact hw _ (by rw [hqv]; omega)
        | exact (hw _ (by rw [hqv]; omega)).symm
  · unfold InNp
    rw [hesI, hqv]
    omega
  · by_cases hlr : l.val + 1 < r
    · have hf : fvec k r z' l.succ = bvec (eI k r ⟨l.val + 1, hlr⟩) := by
        simp only [fvec, Fin.val_succ, dif_pos hlr]
      simp only [Formalism.FourierDecayAlt.Q.xbv, hf, herm_bvec_bvec]
      have hv : (eI k r (⟨l.val + 1, hlr⟩ : Fin r)).val = l.val + 1 := rfl
      simp only [dpsiP, Hpk, Fin.ext_iff, hv, hqv, hesI]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hf : fvec k r z' l.succ = z' := by
        simp only [fvec, Fin.val_succ, dif_neg hlr]
      simp only [Formalism.FourierDecayAlt.Q.xbv, hf]
      rw [dpsiP]
      split_ifs <;> first
        | rfl
        | (exfalso; rw [hqv, hesI] at *; omega)
        | exact hz _ (by rw [hqv]; omega)
        | (exfalso; omega)

theorem herm_unitary {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg']

theorem herm_bvec_eI {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (eI k r b)) = v (esI k r b) := by
  have h1 : herm (Hpk k r) v (bvec (eI k r b)) = ∑ p, Hpk k r (eI k r b) p * v p := by
    have hs : star (bvec (eI k r b)) = bvec (eI k r b) := by
      ext i
      by_cases h : i = eI k r b <;> simp [bvec, Pi.single_apply, h]
    unfold herm
    rw [hs]
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp_rw [hpk_row_eI]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp [esI]
  · intro p _ hp
    rw [if_neg, zero_mul]
    intro h
    exact hp (Fin.ext (by simp [esI, h]))
  · simp

theorem xi_Y_zhat_identity : XiYZhat := by
  intro k r z z' g a b hg
  have hf : ∀ (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r), fvec k r w c.castSucc = bvec (eI k r c) := by
    intro w c
    simp [fvec, c.isLt]
  have hZ : Zhat k r z z' g a.castSucc b.castSucc =
      herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) := by
    simp only [Zhat, hf]
  refine ⟨hZ.symm, ?_⟩
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hdet : IsUnit g.det := by
    have h1 : (Hpk k r).det * (Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, hHH, Matrix.det_one]
    have h2 := congrArg Matrix.det hg'
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at h1
    exact zero_ne_one h1
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have hsym : ∀ v w, star (herm (Hpk k r) v w) = herm (Hpk k r) w v := by
    intro v w
    unfold herm
    first
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]; done)
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec];
        exact Matrix.dotProduct_comm _ _)
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec];
        exact (Matrix.dotProduct_comm _ _).symm)
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_comm,
        Matrix.dotProduct_mulVec]; done)
    | (simp [Matrix.star_dotProduct, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]; done)
  calc (g⁻¹ *ᵥ bvec (eI k r a)) (esI k r b)
      = herm (Hpk k r) (g⁻¹ *ᵥ bvec (eI k r a)) (bvec (eI k r b)) := (herm_bvec_eI _ b).symm
    _ = herm (Hpk k r) (g *ᵥ (g⁻¹ *ᵥ bvec (eI k r a))) (g *ᵥ bvec (eI k r b)) :=
        (herm_unitary g hg _ _).symm
    _ = herm (Hpk k r) (bvec (eI k r a)) (g *ᵥ bvec (eI k r b)) := by
        rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
    _ = star (herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a))) := (hsym _ _).symm
    _ = star (Zhat k r z z' g a.castSucc b.castSucc) := by rw [hZ]

end Formalism.FourierDecayAlt.P.SignAntidiagonal
