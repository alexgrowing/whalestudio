import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)

noncomputable section

namespace RegChartData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
  (R : RegChartData A)

theorem exists_q_lower [CompactSpace X] :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ j, ∀ x ∈ R.mid j, -Q ≤ R.q j (R.chart j x) := by
  have h : ∀ j, ∃ m : ℝ, ∀ x ∈ R.mid j, m ≤ R.q j (R.chart j x) := by
    intro j
    have hK : IsCompact (R.chart j '' closure (R.mid j)) :=
      isClosed_closure.isCompact.image_of_continuousOn
        ((R.chart j).continuousOn.mono (R.closure_mid j))
    have hsub : R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact (R.chart j).map_source (R.closure_mid j hx)
    obtain ⟨m, hm⟩ := hK.bddBelow_image ((R.q_smooth j).continuousOn.mono hsub)
    exact ⟨m, fun x hx => hm ⟨R.chart j x, ⟨x, subset_closure hx, rfl⟩, rfl⟩⟩
  choose m hm using h
  refine ⟨∑ j, |m j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun j x hx => ?_⟩
  have h1 : |m j| ≤ ∑ j, |m j| :=
    Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 := hm j x hx
  linarith [neg_abs_le (m j)]

theorem differentiableAt_u (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : DifferentiableAt ℝ (R.u j) y := by
  have hq : ContDiffAt ℝ ∞ (R.q j) y :=
    (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hy)
  have hph := contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth
    (R.symm_mem_Yo j hy hyA) ((R.chart j).map_target hy)
  rw [(R.chart j).right_inv hy] at hph
  exact (hq.add hph).differentiableAt (by simp)

theorem near_point {t B : ℝ} (ht : 0 < t) (hB : ∀ j, ∀ y ∈ (R.chart j).target, |R.f j y| ≤ B)
    (htB : t ≤ Real.exp (-B) / 4) {j : Fin R.N} {x : X} (hx : x ∈ R.mid j) (hxY : x ∈ R.Yo)
    (hr : R.r x ≤ Real.log t⁻¹) {y : Fin D → ℂ} (hy : y ∈ closedBall (R.chart j x) t)
    (hyT : y ∈ (R.chart j).target) :
    y ∉ coordDiv (R.S j) ∧
      R.r ((R.chart j).symm y) ≤ Real.log t⁻¹ + (2 * B + D * Real.log 4) := by
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j hx
  obtain ⟨z, hz⟩ : ∃ z, z = R.chart j x := ⟨_, rfl⟩
  rw [← hz] at hy
  have hzT : z ∈ (R.chart j).target := hz ▸ (R.chart j).map_source hxs
  have hzA : z ∉ coordDiv (R.S j) := hz ▸ (R.mem_Yo j x hxs).1 hxY
  have hzx : (R.chart j).symm z = x := hz ▸ (R.chart j).left_inv hxs
  have hrx : R.r x = Real.exp 1 + R.f j z + ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)⁻¹ := by
    have := R.r_chart j z ⟨hzT, hzA⟩
    rwa [hzx] at this
  have hnn : ∀ w ∈ (R.chart j).target, ∀ i, 0 ≤ Real.log (‖w i‖ ^ 2)⁻¹ := by
    intro w hw i
    have hw1 : ‖w‖ < 1 := by simpa using R.target_subset j hw
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (by positivity)
      (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm w i).trans hw1.le)))
  have hsum : ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)⁻¹ ≤ Real.log t⁻¹ + B := by
    have h1 := hB j z hzT
    have h2 := neg_abs_le (R.f j z)
    have h3 := Real.exp_pos 1
    linarith
  have hzi : ∀ i ∈ R.S j, 2 * t ≤ ‖z i‖ := by
    intro i hi
    have hpos : 0 < ‖z i‖ := norm_pos_iff.2 fun h0 => hzA ⟨i, hi, h0⟩
    have hle : Real.log (‖z i‖ ^ 2)⁻¹ ≤ Real.log t⁻¹ + B :=
      (Finset.single_le_sum (f := fun i => Real.log (‖z i‖ ^ 2)⁻¹) (fun i _ => hnn z hzT i) hi).trans
        hsum
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hE := Real.exp_pos (-B)
    have h4 : 4 * t * t ≤ t * Real.exp (-B) := by nlinarith
    have ha : ‖z i‖ ^ 2 < t * Real.exp (-B) := by nlinarith
    have hlog : Real.log t⁻¹ + B < Real.log (‖z i‖ ^ 2)⁻¹ := by
      have h1 : Real.log (t * Real.exp (-B))⁻¹ = Real.log t⁻¹ + B := by
        rw [Real.log_inv, Real.log_mul ht.ne' hE.ne', Real.log_exp, Real.log_inv]; ring
      rw [← h1]
      exact Real.log_lt_log (by positivity) ((inv_lt_inv₀ (by positivity) (by positivity)).2 ha)
    linarith
  have hyz : ∀ i, ‖z i‖ ≤ ‖y i‖ + t := by
    intro i
    have h1 : ‖y i - z i‖ ≤ t :=
      (norm_le_pi_norm (y - z) i).trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hy)
    have h2 := norm_sub_norm_le (z i) (y i)
    rw [norm_sub_rev] at h2
    linarith
  have hyi : ∀ i ∈ R.S j, ‖z i‖ / 2 ≤ ‖y i‖ := fun i hi => by linarith [hzi i hi, hyz i]
  have hyA : y ∉ coordDiv (R.S j) := by
    rintro ⟨i, hi, h0⟩
    have h3 : ‖y i‖ = 0 := by rw [h0, norm_zero]
    linarith [hyi i hi, hzi i hi]
  refine ⟨hyA, ?_⟩
  have hterm : ∀ i ∈ R.S j,
      Real.log (‖y i‖ ^ 2)⁻¹ ≤ Real.log (‖z i‖ ^ 2)⁻¹ + Real.log 4 := by
    intro i hi
    have hzp : 0 < ‖z i‖ := by linarith [hzi i hi]
    have hyp : 0 < ‖y i‖ := by linarith [hyi i hi]
    rw [Real.log_inv, Real.log_inv]
    have : Real.log (‖z i‖ ^ 2) - Real.log 4 ≤ Real.log (‖y i‖ ^ 2) := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) (by nlinarith [hyi i hi])
    linarith
  have hS : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤
      ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)⁻¹ + D * Real.log 4 := by
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ((R.S j).card : ℝ) ≤ D := by
      have := Finset.card_le_univ (R.S j)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have h3 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  rw [R.r_chart j y ⟨hyT, hyA⟩]
  have h1 := hB j y hyT
  have h2 := le_abs_self (R.f j y)
  have h3 := hB j z hzT
  have h4 := neg_abs_le (R.f j z)
  linarith

end RegChartData

theorem MollifiedNearSmooth.proof (h : TruncPsh.Statement) : MollifiedNearSmooth.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B₀, hδ, hV⟩ := h X D A R
  choose V hVo hVt hVball hVpsh using hV
  obtain ⟨Q, hQ0, hQ⟩ := R.exists_q_lower
  obtain ⟨B, hB⟩ := R.f_bdd
  obtain ⟨B', hB'⟩ : ∃ b : ℝ, b = max B 0 := ⟨_, rfl⟩
  have hB'0 : 0 ≤ B' := hB' ▸ le_max_right _ _
  have hfB : ∀ j, ∀ y ∈ (R.chart j).target, |R.f j y| ≤ B' :=
    fun j y hy => (hB j y hy).trans (hB' ▸ le_max_left _ _)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * B' + D * Real.log 4 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ add_nonneg (by linarith)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
  obtain ⟨G, hG⟩ : ∃ g : ℝ, g = |R.Cgrad| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ abs_nonneg _
  obtain ⟨Cl, hCl⟩ : ∃ g : ℝ, g = |R.Clog| := ⟨_, rfl⟩
  have hCl0 : 0 ≤ Cl := hCl ▸ abs_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max (G * 2 ^ G * Real.exp (c / 2)) (max G (Q + Cl)) := ⟨_, rfl⟩
  have hC1 : G * 2 ^ G * Real.exp (c / 2) ≤ C := hC ▸ le_max_left _ _
  have hC2 : G ≤ C := hC ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Q + Cl ≤ C := hC ▸ (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, min (min δ (Real.exp (-B') / 4)) (Real.exp (-(Real.exp 1 + 2 * c))),
    lt_min (lt_min hδ (by positivity)) (Real.exp_pos _), ?_⟩
  intro t ht ht₀ K hK j x hx hrx
  simp only [lt_min_iff] at ht₀
  obtain ⟨⟨htδ, htB⟩, hte⟩ := ht₀
  obtain ⟨hℓc, hlogℓ⟩ := log_inv_facts ht hc0 hte
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hℓ1 : 1 ≤ Real.log t⁻¹ := by linarith
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j hx.1
  have hballV : closedBall (R.chart j x) t ⊆ V j :=
    (closedBall_subset_closedBall htδ.le).trans (hVball j x hx.1)
  have hballT : closedBall (R.chart j x) t ⊆ (R.chart j).target := hballV.trans (hVt j)
  have hnear := fun y (hy : y ∈ closedBall (R.chart j x) t) =>
    R.near_point ht hfB htB.le hx.1 hx.2 hrx hy (hballT hy)
  rw [← hc] at hnear

  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = G * (Real.log t⁻¹ + c) ^ G * Real.exp ((Real.log t⁻¹ + c) / 2) :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ by positivity
  have hgrad : ∀ y ∈ closedBall (R.chart j x) t, ‖fderiv ℝ (R.u j) y‖ ≤ M := by
    intro y hy
    obtain ⟨hyA, hry⟩ := hnear y hy
    have hyT := hballT hy
    have h1r : 1 ≤ R.r ((R.chart j).symm y) := R.one_le_r _ (R.symm_mem_Yo j hyT hyA)
    have hg := R.grad_le j y ⟨hyT, hyA⟩
    have e1 : R.Cgrad * R.r ((R.chart j).symm y) ^ R.Cgrad ≤ G * R.r ((R.chart j).symm y) ^ G :=
      (mul_le_mul_of_nonneg_right (hG ▸ le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1r (hG ▸ le_abs_self _)) hG0)
    have e2 : R.r ((R.chart j).symm y) ^ G ≤ (Real.log t⁻¹ + c) ^ G :=
      Real.rpow_le_rpow (by linarith) hry hG0
    have e3 : Real.exp (R.r ((R.chart j).symm y) / 2) ≤ Real.exp ((Real.log t⁻¹ + c) / 2) :=
      Real.exp_le_exp.2 (by linarith)
    refine hg.trans ?_
    rw [hM]
    calc R.Cgrad * R.r ((R.chart j).symm y) ^ R.Cgrad * Real.exp (R.r ((R.chart j).symm y) / 2)
        ≤ G * R.r ((R.chart j).symm y) ^ G * Real.exp (R.r ((R.chart j).symm y) / 2) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ ≤ G * (Real.log t⁻¹ + c) ^ G * Real.exp ((Real.log t⁻¹ + c) / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left e2 hG0) e3 (Real.exp_pos _).le (by positivity)

  have hmv : ∀ y ∈ closedBall (R.chart j x) t, R.u j y ≤ R.u j (R.chart j x) + M * t := by
    intro y hy
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y' hy' => R.differentiableAt_u j (hballT hy') (hnear y' hy').1) hgrad
      (convex_closedBall _ t) (mem_closedBall_self ht.le) hy
    have h2 : ‖y - R.chart j x‖ ≤ t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    have h3 := le_abs_self (R.u j y - R.u j (R.chart j x))
    rw [← Real.norm_eq_abs] at h3
    nlinarith [mul_le_mul_of_nonneg_left h2 hM0]

  have huz : -K ≤ R.u j (R.chart j x) := by
    have hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x := by
      show R.q j (R.chart j x) + R.ph ((R.chart j).symm (R.chart j x)) = _
      rw [(R.chart j).left_inv hxs]
    have hr1 : 1 ≤ R.r x := R.one_le_r x hx.2
    have hL0 : 0 ≤ Real.log (R.r x) := Real.log_nonneg hr1
    have hL : Real.log (R.r x) ≤ Real.log (Real.log t⁻¹) := Real.log_le_log (by linarith) hrx
    have hph := R.ph_ge x hx.2
    have e1 : R.Clog * Real.log (R.r x) ≤ Cl * Real.log (Real.log t⁻¹) :=
      (mul_le_mul_of_nonneg_right (hCl ▸ le_abs_self _) hL0).trans (mul_le_mul_of_nonneg_left hL hCl0)
    have e2 : Q ≤ Q * Real.log (Real.log t⁻¹) := le_mul_of_one_le_right hQ0 hlogℓ.le
    have e3 : (Q + Cl) * Real.log (Real.log t⁻¹) ≤ C * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hC3 (by linarith)
    have e4 := hQ j x hx.1
    have e5 : -R.Clog * Real.log (R.r x) = -(R.Clog * Real.log (R.r x)) := by ring
    have e6 : (Q + Cl) * Real.log (Real.log t⁻¹) =
        Q * Real.log (Real.log t⁻¹) + Cl * Real.log (Real.log t⁻¹) := by ring
    linarith

  have hbound : M * t ≤ C * Real.log t⁻¹ ^ C * t ^ (1 / 2 : ℝ) := by
    have ht' : Real.exp (Real.log t⁻¹ / 2) * t = t ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos ht, Real.log_inv]
      calc Real.exp (-Real.log t / 2) * t = Real.exp (-Real.log t / 2) * Real.exp (Real.log t) := by
            rw [Real.exp_log ht]
        _ = Real.exp (Real.log t * (1 / 2)) := by
            rw [← Real.exp_add]
            congr 1
            ring
    have hMt : M * t = G * (Real.log t⁻¹ + c) ^ G * Real.exp (c / 2) * t ^ (1 / 2 : ℝ) := by
      rw [hM, ← ht', show (Real.log t⁻¹ + c) / 2 = Real.log t⁻¹ / 2 + c / 2 by ring, Real.exp_add]
      ring
    have e4 : (Real.log t⁻¹ + c) ^ G ≤ 2 ^ G * Real.log t⁻¹ ^ G := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hG0
    have e5 : Real.log t⁻¹ ^ G ≤ Real.log t⁻¹ ^ C := Real.rpow_le_rpow_of_exponent_le hℓ1 hC2
    have hs : 0 ≤ t ^ (1 / 2 : ℝ) := by positivity
    rw [hMt]
    calc G * (Real.log t⁻¹ + c) ^ G * Real.exp (c / 2) * t ^ (1 / 2 : ℝ)
        ≤ G * (2 ^ G * Real.log t⁻¹ ^ G) * Real.exp (c / 2) * t ^ (1 / 2 : ℝ) := by gcongr
      _ = G * 2 ^ G * Real.exp (c / 2) * Real.log t⁻¹ ^ G * t ^ (1 / 2 : ℝ) := by ring
      _ ≤ C * Real.log t⁻¹ ^ C * t ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hC1 e5 (by positivity) (by linarith)) hs

  have hi : molli ρ t (R.trunc K j) (R.chart j x) ≤ polyMax (R.trunc K j) (R.chart j x) t :=
    (((mollify_thm D ρ (V j) (R.trunc K j) (hVo j) (hVpsh j K).1).1 t ht).2.2.2
      (R.chart j x) hballV).2
  have hii : polyMax (R.trunc K j) (R.chart j x) t ≤ R.u j (R.chart j x) + M * t :=
    polyMax_le' ht.le fun y hy => by
      have hyA := (hnear y hy).1
      simp only [RegChartData.trunc, limsupExt, if_neg hyA]
      exact max_le (hmv y hy) (by nlinarith)
  simp only [RegChartData.smoothed]
  linarith

end

end GroundTheory.Heights₂.Heights.Regular
