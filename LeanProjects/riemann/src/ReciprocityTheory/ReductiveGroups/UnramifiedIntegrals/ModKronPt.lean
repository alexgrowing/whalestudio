import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDeltaInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQExpEq
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronSer

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def kronFun (p : ℕ) (τ : ℍ) : ℂ := Gm p τ + (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2

theorem kronSq_isMF (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)

theorem Gm_isMF' {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := (gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)

theorem kronFun_isMF {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (kronFun p) := (Gm_isMF' hp).add (kronSq_isMF p)

theorem aC_conv : Conv aC := convergesOnDisk_eisensteinFourCubeSeries
theorem dC_conv : Conv dC := convergesOnDisk_discriminantSeries
theorem aC_ev (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  exact evalSeries_eisensteinFourCubeSeries τ
theorem dC_ev (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  exact evalSeries_discriminantSeries τ

theorem kronFun_qExp {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl

theorem kronFun_div {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ qExpansion 1 (kronFun p) = PowerSeries.C (1 - zetaC p) * w := by
  obtain ⟨w, hw, hk⟩ := kronSer hp
  have hp0 : 0 < p := hp.pos
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩
  rw [kronFun_qExp hp]
  ext n
  have key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) =
      PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    simp [xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]
  have hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) =
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    rw [← gmQ_xp hp0]
    ext m
    simp only [xp, PowerSeries.coeff_mk, map_add]
    split_ifs <;> simp
  rw [← key, hsum, hk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

theorem kronFun_poly {p : ℕ} (hp : p.Prime) :
    ∃ Q : Polynomial ℂ, (∀ i, Q.coeff i ∈ Rm p) ∧
      ∀ τ, kronFun p τ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * Q.eval (jT τ)) := by
  obtain ⟨w, hw, hqe⟩ := kronFun_div hp
  have hc0 : (1 - zetaC p) ≠ 0 := one_sub_zeta_ne_zero hp
  have hK := kronFun_isMF hp
  let f : ℍ → ℂ := fun τ => (1 - zetaC p)⁻¹ * kronFun p τ
  have hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f := hK.const_mul (1 - zetaC p)⁻¹
  have hwq : qExpansion 1 f = w := by
    apply hf.qExp_eq
    · have e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p) := by
        rw [hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [e]
      exact hK.conv.C_mul _
    · intro τ
      have hs := (hK.hasSum τ).mul_left (1 - zetaC p)⁻¹
      have hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n =
          (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n) := by
        intro n
        rw [hqe, PowerSeries.coeff_C_mul]
        field_simp
      unfold ev
      simp_rw [hw']
      exact hs.tsum_eq
  obtain ⟨P, hPc, -, hPe⟩ := qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)
  refine ⟨P, hPc, fun τ => ?_⟩
  calc kronFun p τ = (1 - zetaC p) * f τ := by
        rw [show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]

theorem kronPt {p : ℕ} (hp : p.Prime) {τ : ℍ} (h : Gm p τ = 0) :
    ∃ r : ℂ, IsIntegral ℤ r ∧ (jT τ ^ p - jT τ) ^ 2 = (1 - zetaC p) * r := by
  obtain ⟨Q, hQ, hK⟩ := kronFun_poly hp
  have hD := DD_ne_zero τ
  have hsq : ¬ IsSquare p := Irreducible.not_isSquare hp
  have hj := jT_isIntegral hp.pos hsq h
  have hint : IsIntegral ℤ (Q.eval (jT τ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)
  refine ⟨Q.eval (jT τ), hint, ?_⟩
  have e1 := hK τ
  unfold kronFun at e1
  rw [h, zero_add] at e1
  have hA : AA τ = jT τ * DD τ := by rw [jT, div_mul_cancel₀ _ hD]
  rw [hA] at e1
  have e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) =
      (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1)) := by
    linear_combination e1
  exact mul_right_cancel₀ (pow_ne_zero _ hD) e2

end ReciprocityTheory.ChartRestriction.L1
