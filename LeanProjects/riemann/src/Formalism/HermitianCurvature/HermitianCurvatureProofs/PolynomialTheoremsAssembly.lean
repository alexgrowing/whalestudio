import Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondPolynomialClauses

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem thGrid_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) :
    0 ≤ F7.thGrid grid j := by
  unfold F7.thGrid
  exact Finset.prod_nonneg fun b _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)

theorem sum_abs_coProd {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j, |coProd grid j| = ∏ a, cg grid a := by
  simp only [coProd, Finset.abs_prod, cg]
  exact (Fintype.prod_sum (fun a i => |F7.lagCo (grid a) i|)).symm

theorem lamPSq_ge {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (Rw ZZ : ℝ) (a : Fin K) :
    cg grid a ^ 2 * Rw * ZZ ≤ lamPSq grid Rw ZZ := by
  unfold lamPSq
  rw [Finset.le_fold_max]
  exact Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩

theorem lamPSq_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (Rw ZZ : ℝ) :
    0 ≤ lamPSq grid Rw ZZ := by
  unfold lamPSq
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

theorem p3aOfParts_ok : LeadingBlockRecursiveBoundFromComponents := by
  intro V _ _ K d grid q x nn w e t X0 XK ρ E wt bw Rw ZZ hg he ht hpos hTop hFS hR hZ hwt hbw
  obtain ⟨hρ, -, hE⟩ := hFS
  unfold LeadingCoefficientVectorIdentity at hTop
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have he1 : ‖e‖ = 1 := by rcases he with h | h <;> simp [h]
  have h1 : ‖t‖⁻¹ ^ K * ‖X0‖ ≤ ∑ j, |coProd grid j| * ‖XK j‖ := by
    have : ‖(e / t) ^ K • X0‖ = ‖t‖⁻¹ ^ K * ‖X0‖ := by rw [norm_smul, norm_pow, norm_div, he1, one_div]
    rw [← this, hTop]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hCS : (∑ j, |coProd grid j| * ‖XK j‖) ^ 2 ≤
      (∑ j, |coProd grid j|) * ∑ j, |coProd grid j| * ‖XK j‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Real.sqrt |coProd grid j|)
      (fun j => Real.sqrt |coProd grid j| * ‖XK j‖)
    have hs : ∀ j, Real.sqrt |coProd grid j| * (Real.sqrt |coProd grid j| * ‖XK j‖) = |coProd grid j| * ‖XK j‖ :=
      fun j => by rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have hs2 : ∀ j, Real.sqrt |coProd grid j| ^ 2 = |coProd grid j| := fun j => Real.sq_sqrt (abs_nonneg _)
    have hs3 : ∀ j, (Real.sqrt |coProd grid j| * ‖XK j‖) ^ 2 = |coProd grid j| * ‖XK j‖ ^ 2 :=
      fun j => by rw [mul_pow, hs2]
    simp only [hs, hs2, hs3] at h
    exact h
  have hnn : ∀ j, (∏ b, nn (grid b (j b))) ≤ (∏ _b : Fin K, (Rw * ZZ)) * ∏ b, ρ b j := by
    intro j
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun b _ => (hpos b (j b)).2.1.le)
    intro b _
    have hq := (hpos b (j b)).1
    have hnb := (hpos b (j b)).2.1
    have hx0 : 0 < |x (grid b (j b) + 1)| := abs_pos.mpr (hpos b (j b)).2.2
    have h1 := hR b j
    have h2 := hZ b (j b)
    have hZ0 : 0 ≤ ZZ := le_trans (div_nonneg (mul_nonneg hnb.le hx0.le) hq.le) h2
    have hqne := hq.ne'
    have hxne := hx0.ne'
    calc nn (grid b (j b)) = (nn (grid b (j b)) * |x (grid b (j b) + 1)| / q (grid b (j b))) *
          (q (grid b (j b)) / |x (grid b (j b) + 1)|) := by field_simp
      _ ≤ ZZ * (Rw * ρ b j) := mul_le_mul h2 h1 (div_nonneg hq.le hx0.le) hZ0
      _ = Rw * ZZ * ρ b j := by ring
  have hn0 : ∀ j, 0 < nnProd nn 0 grid j := fun j =>
    Finset.prod_pos fun b _ => by simpa using (hpos b (j b)).2.1
  have hP0 : 0 < ∏ _b : Fin K, (Rw * ZZ) := by
    have h := hnn (fun _ => 0)
    have h1 : 0 < ∏ b, nn (grid b ((fun _ => (0 : Fin (d + 1))) b)) :=
      Finset.prod_pos fun b _ => (hpos b _).2.1
    have h2 : 0 < ∏ b, ρ b (fun _ => 0) := Finset.prod_pos fun b _ => hρ b _
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hE0 : ∀ j, 0 ≤ E j := fun j =>
    le_trans (mul_nonneg (Finset.prod_pos fun b _ => hρ b j).le (sq_nonneg _)) (hE j)
  have hXK : ∀ j, ‖XK j‖ ^ 2 ≤ (∏ _b : Fin K, (Rw * ZZ)) * (E j / nnProd nn 0 grid j) := by
    intro j
    have hnn' : nnProd nn 0 grid j ≤ (∏ _b : Fin K, (Rw * ZZ)) * ∏ b, ρ b j := by
      simpa [nnProd] using hnn j
    rw [mul_div_assoc', le_div_iff₀ (hn0 j)]
    calc ‖XK j‖ ^ 2 * nnProd nn 0 grid j
        ≤ ‖XK j‖ ^ 2 * ((∏ _b : Fin K, (Rw * ZZ)) * ∏ b, ρ b j) :=
          mul_le_mul_of_nonneg_left hnn' (sq_nonneg _)
      _ = (∏ _b : Fin K, (Rw * ZZ)) * ((∏ b, ρ b j) * ‖XK j‖ ^ 2) := by ring
      _ ≤ (∏ _b : Fin K, (Rw * ZZ)) * E j := mul_le_mul_of_nonneg_left (hE j) hP0.le
  have hth := Formalism.FourierDecayAlt.P.SecondPolynomialClauses.co_eq grid hg
  have step : (‖t‖⁻¹ ^ K) ^ 2 * ‖X0‖ ^ 2 ≤ (∏ a, cg grid a) ^ 2 *
      ((∏ _b : Fin K, (Rw * ZZ)) * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j)) := by
    have hm0 : 0 ≤ ‖t‖⁻¹ ^ K * ‖X0‖ := by positivity
    calc (‖t‖⁻¹ ^ K) ^ 2 * ‖X0‖ ^ 2 = (‖t‖⁻¹ ^ K * ‖X0‖) ^ 2 := by ring
      _ ≤ (∑ j, |coProd grid j| * ‖XK j‖) ^ 2 := pow_le_pow_left₀ hm0 h1 2
      _ ≤ (∑ j, |coProd grid j|) * ∑ j, |coProd grid j| * ‖XK j‖ ^ 2 := hCS
      _ = (∏ a, cg grid a) * ∑ j, (∏ a, cg grid a) * F7.thGrid grid j * ‖XK j‖ ^ 2 := by
          rw [sum_abs_coProd]; simp only [hth]
      _ = (∏ a, cg grid a) ^ 2 * ∑ j, F7.thGrid grid j * ‖XK j‖ ^ 2 := by
          rw [sq, mul_assoc]; congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ (∏ a, cg grid a) ^ 2 * ∑ j, F7.thGrid grid j *
            ((∏ _b : Fin K, (Rw * ZZ)) * (E j / nnProd nn 0 grid j)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hXK j) (thGrid_nonneg grid j))
            (sq_nonneg _)
      _ = (∏ a, cg grid a) ^ 2 *
            ((∏ _b : Fin K, (Rw * ZZ)) * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j)) := by
          congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hz : ‖t‖ ^ (-(2 * K : ℤ)) = (‖t‖⁻¹ ^ K) ^ 2 := by
    rw [← pow_mul, inv_pow, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have hprod : ∏ a, (cg grid a ^ 2 * Rw * ZZ) = (∏ a, cg grid a) ^ 2 * ∏ _b : Fin K, (Rw * ZZ) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro a _; ring
  have hsum : ∑ j, F7.thGrid grid j * (wt ^ 2 * E j / (bw * nnProd nn 0 grid j)) =
      wt ^ 2 / bw * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_div_mul_comm]; ring
  rw [hz, hprod, hsum]
  calc (‖t‖⁻¹ ^ K) ^ 2 * (wt ^ 2 * ‖X0‖ ^ 2 / bw) = wt ^ 2 / bw * ((‖t‖⁻¹ ^ K) ^ 2 * ‖X0‖ ^ 2) := by ring
    _ ≤ wt ^ 2 / bw * ((∏ a, cg grid a) ^ 2 *
          ((∏ _b : Fin K, (Rw * ZZ)) * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j))) :=
        mul_le_mul_of_nonneg_left step (div_nonneg (sq_nonneg _) hbw.le)
    _ = (∏ a, cg grid a) ^ 2 * (∏ _b : Fin K, (Rw * ZZ)) *
          (wt ^ 2 / bw * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j)) := by ring

theorem lower_block_lift_bound_reduction : LowerBlockLiftBoundFromComponents := by
  intro hA hU hC V _ _ R x ex K d grid q nn w e t t' W RL RV bw Qw BB hR hbw ht ht' he hg hpos hQ hB hBB
    hRL hD hS
  have hb := hU K d grid q w e (1 / t - 1 / t') (R (x t) (x t')) W RL RV he
    (fun j => Finset.prod_pos fun a _ => (hpos a (j a)).2.1) hRL hD hS
  have hc := hC K d grid q nn w (1 / t - 1 / t') (R (x t) (x t')) RL RV (‖t‖ ^ ex) (‖t'‖ ^ ex) bw Qw BB
    hg hpos hQ hB hBB (by positivity) (by positivity) hbw hRL hb
  have hN : ‖Npair R x (fun u => ‖u‖ ^ ex) bw t t'‖ = ‖t‖ ^ ex * ‖t'‖ ^ ex / bw * ‖R (x t) (x t')‖ := by
    unfold Npair
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by positivity) hbw.le)]
  refine ⟨hA V R x (fun u => ‖u‖ ^ ex) bw hR hbw (fun u => by positivity) t t', hb, ?_⟩
  rw [hN]
  simp only [pow_mul']
  exact hc

theorem leading_block_lift_bound_reduction : LeadingBlockLiftBoundFromComponents := by
  intro hA hB V _ _ ex K d grid q x nn w e t t' Ntt X0 XK ρ E bw Rw ZZ hg he ht ht' hpos hTop hFS hR hZ
    hRw hZZ hbw hG
  have ha := hA V K d grid q x nn w e t (X0 t) XK ρ E (‖t‖ ^ ex) bw Rw ZZ hg he ht hpos hTop hFS hR hZ
    (by positivity) hbw
  have hpw : (‖t‖ ^ ex) ^ 2 = ‖t‖ ^ (2 * ex) := by rw [← pow_mul, mul_comm]
  rw [hpw] at ha
  refine ⟨ha, fun ho hle => ?_⟩
  have hE0 : ∀ j, 0 ≤ E j := fun j =>
    le_trans (mul_nonneg (Finset.prod_pos fun b _ => hFS.1 b j).le (sq_nonneg _)) (hFS.2.2 j)
  have hn0 : ∀ j, 0 < nnProd nn 0 grid j := fun j =>
    Finset.prod_pos fun b _ => by simpa using (hpos b (j b)).2.1
  have hS : 0 ≤ ∑ j, F7.thGrid grid j * (‖t‖ ^ (2 * ex) * E j / (bw * nnProd nn 0 grid j)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (thGrid_nonneg grid j)
      (div_nonneg (mul_nonneg (by positivity) (hE0 j)) (mul_pos hbw (hn0 j)).le)
  refine hB K t t' Ntt (‖t‖ ^ (2 * ex) * ‖X0 t‖ ^ 2 / bw) (‖t'‖ ^ (2 * ex) * ‖X0 t'‖ ^ 2 / bw)
    (∑ j, F7.thGrid grid j * (‖t‖ ^ (2 * ex) * E j / (bw * nnProd nn 0 grid j)))
    (Real.sqrt (lamPSq grid Rw ZZ)) (fun a => cg grid a ^ 2 * Rw * ZZ) ht ht' ho hle
    (div_nonneg (by positivity) hbw.le) (div_nonneg (by positivity) hbw.le) hS (Real.sqrt_nonneg _)
    (fun a => ⟨by positivity, ?_⟩) hG ha
  rw [Real.sq_sqrt (lamPSq_nonneg grid Rw ZZ)]
  exact lamPSq_ge grid Rw ZZ a

end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly

theorem Formalism.FourierDecayAlt.P.leading_block_recursive_bound_of_components : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockRecursiveBoundFromComponents := Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.p3aOfParts_ok
theorem Formalism.FourierDecayAlt.P.lower_block_lift_bound_of_components : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockLiftBoundFromComponents := Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lower_block_lift_bound_reduction
theorem Formalism.FourierDecayAlt.P.leading_block_lift_bound_of_components : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockLiftBoundFromComponents := Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.leading_block_lift_bound_reduction

theorem Formalism.FourierDecayAlt.P.lower_block_lift_bound : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockLiftBound :=
  Formalism.FourierDecayAlt.P.lower_block_lift_bound_of_components Formalism.FourierDecayAlt.P.second_polynomial_first_identity Formalism.FourierDecayAlt.P.unipotent_degree_three_of_clauses
    Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts

theorem Formalism.FourierDecayAlt.P.leading_block_lift_bound : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockLiftBound :=
  Formalism.FourierDecayAlt.P.leading_block_lift_bound_of_components Formalism.FourierDecayAlt.P.leading_block_recursive_bound_of_components Formalism.FourierDecayAlt.P.third_polynomial_second_of_first

end
