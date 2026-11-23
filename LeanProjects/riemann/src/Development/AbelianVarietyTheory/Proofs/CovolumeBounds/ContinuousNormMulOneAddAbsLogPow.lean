import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NeZeroOnHyperplaneOfEventuallyNeZero

open Matrix Set
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory

section

open Filter Metric Function Asymptotics
open scoped Topology

theorem continuous_norm_mul_one_add_abs_log_pow (N : ℕ) :
    Continuous fun t : ℂ => ‖t‖ * (1 + |Real.log ‖t‖|) ^ (N + 1) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    have hn : Tendsto (fun t : ℂ => ‖t‖) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuous_norm.tendsto' 0 0 norm_zero).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact norm_ne_zero_iff.mpr ht
    have hv : Tendsto (fun t : ℂ => 1 - Real.log ‖t‖) (𝓝[≠] 0) atTop := by
      have := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp hn)
      exact (tendsto_atTop_add_const_left _ 1 this).congr fun t => by
        simp only [Function.comp_apply]; ring
    have hlim := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (N + 1)).comp hv).const_mul
      (Real.exp 1)
    rw [mul_zero] at hlim
    have hmain : Tendsto (fun t : ℂ => ‖t‖ * (1 + |Real.log ‖t‖|) ^ (N + 1)) (𝓝[≠] 0) (𝓝 0) := by
      refine hlim.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos),
        self_mem_nhdsWithin] with t h1 h2
      have hpos : 0 < ‖t‖ := norm_pos_iff.mpr h2
      have hle : ‖t‖ ≤ 1 := by simpa using h1
      have hlog : Real.log ‖t‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hle
      simp only [Function.comp_apply]
      rw [abs_of_nonpos hlog, show -(1 - Real.log ‖t‖) = -1 + Real.log ‖t‖ by ring, Real.exp_add,
        Real.exp_log hpos]
      have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
      calc Real.exp 1 * ((1 - Real.log ‖t‖) ^ (N + 1) * (Real.exp (-1) * ‖t‖))
          = (Real.exp 1 * Real.exp (-1)) * (‖t‖ * (1 - Real.log ‖t‖) ^ (N + 1)) := by ring
        _ = ‖t‖ * (1 + -Real.log ‖t‖) ^ (N + 1) := by rw [he, one_mul, sub_eq_add_neg]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    convert hmain using 2
    simp
  · have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    exact continuous_norm.continuousAt.mul
      ((continuousAt_const.add ((Real.continuousAt_log hn).comp continuous_norm.continuousAt).abs).pow _)

theorem logWeight_le_prod {κ : Type*} (S : Finset κ) (z : κ → ℂ) :
    lwP₂ S z ≤ ∏ j ∈ S, (1 + |Real.log ‖z j‖|) := by
  classical
  show 1 + ∑ j ∈ S, |Real.log ‖z j‖| ≤ _
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ j ∈ s, |Real.log ‖z j‖| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have ha0 := abs_nonneg (Real.log ‖z a‖)
    have h1 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + |Real.log ‖z a‖|)
    nlinarith [mul_nonneg ha0 h0]

theorem HasLogGrowth.tendsto_prod_mul {κ X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {S : Finset κ} {w : X → κ → ℂ} {U : Set X} (hU : IsOpen U) {f : X → ℂ}
    (hf : HasLogGrowth S w U f) {p : X} (hp : p ∈ U) (hB : p ∈ coordDivisor S w)
    (hw : ∀ j ∈ S, ContinuousAt (fun x => w x j) p) :
    Tendsto (fun x => (∏ j ∈ S, w x j) * f x) (𝓝 p) (𝓝 0) := by
  obtain ⟨K, hK, hpK, hKU⟩ := exists_compact_subset hU hp
  obtain ⟨C, N, hC, hb⟩ := hf.exists_one_le hKU hK
  obtain ⟨k, hkS, hk0⟩ := hB
  have hφ := continuous_norm_mul_one_add_abs_log_pow N
  have hg : Tendsto (fun x => C * ∏ j ∈ S, (‖w x j‖ * (1 + |Real.log ‖w x j‖|) ^ (N + 1)))
      (𝓝 p) (𝓝 0) := by
    have : Tendsto (fun x => C * ∏ j ∈ S, (‖w x j‖ * (1 + |Real.log ‖w x j‖|) ^ (N + 1))) (𝓝 p)
        (𝓝 (C * ∏ j ∈ S, (‖w p j‖ * (1 + |Real.log ‖w p j‖|) ^ (N + 1)))) :=
      tendsto_const_nhds.mul (tendsto_finsetProd _ fun j hj => (hφ.tendsto _).comp (hw j hj).tendsto)
    rwa [Finset.prod_eq_zero hkS (by simp [hk0]), mul_zero] at this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [mem_interior_iff_mem_nhds.mp hpK] with x hx
  by_cases hxB : x ∈ coordDivisor S w
  · rw [mem_coordDivisor_iff_prod_eq_zero.mp hxB, zero_mul, norm_zero]
    exact mul_nonneg (by linarith) (Finset.prod_nonneg fun j _ => by positivity)
  · have hfx := hb x hx hxB
    have hW := logWeight_le_prod S (w x)
    have hW0 : 0 ≤ GlobalTheory.lwP₂ S (w x) := (logWeight_pos S (w x)).le
    have h1 : ‖f x‖ ≤ C * ∏ j ∈ S, (1 + |Real.log ‖w x j‖|) ^ (N + 1) := by
      calc ‖f x‖ ≤ C * GlobalTheory.lwP₂ S (w x) ^ N := hfx
        _ ≤ C * (∏ j ∈ S, (1 + |Real.log ‖w x j‖|)) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW N) (by linarith)
        _ = C * ∏ j ∈ S, (1 + |Real.log ‖w x j‖|) ^ N := by rw [Finset.prod_pow]
        _ ≤ C * ∏ j ∈ S, (1 + |Real.log ‖w x j‖|) ^ (N + 1) := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun j _ => by positivity)
              fun j _ => pow_le_pow_right₀ ?_ (Nat.le_succ N)) (by linarith)
            linarith [abs_nonneg (Real.log ‖w x j‖)]
    calc ‖(∏ j ∈ S, w x j) * f x‖ = (∏ j ∈ S, ‖w x j‖) * ‖f x‖ := by rw [norm_mul, norm_prod]
      _ ≤ (∏ j ∈ S, ‖w x j‖) * (C * ∏ j ∈ S, (1 + |Real.log ‖w x j‖|) ^ (N + 1)) :=
          mul_le_mul_of_nonneg_left h1 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = C * ∏ j ∈ S, (‖w x j‖ * (1 + |Real.log ‖w x j‖|) ^ (N + 1)) := by
          rw [Finset.prod_mul_distrib]; ring

variable {ι : Type*} [Fintype ι] {S : Finset ι} {U : Set (ι → ℂ)}

private theorem tendsto_ite_eq_zero_nhds_zero {α : Type*} (p : α → ℂ) :
    Tendsto (fun t : ℂ => fun j => if p j = 0 then t else p j) (𝓝 0) (𝓝 p) := by
  have hc : Continuous (fun t : ℂ => fun j => if p j = 0 then t else p j) :=
    continuous_pi fun j => by split_ifs <;> fun_prop
  refine hc.tendsto' 0 p ?_
  funext j
  split_ifs with h
  exacts [h.symm, rfl]

private theorem ite_eq_zero_notMem_coordDivisor {α : Type*} (S : Finset α) (p : α → ℂ) {t : ℂ} (ht : t ≠ 0) :
    (fun j => if p j = 0 then t else p j) ∉ coordDivisor S id := by
  rw [notMem_coordDivisor]
  intro j _
  show (if p j = 0 then t else p j) ≠ 0
  split_ifs with h
  exacts [ht, h]

theorem HasLogGrowth.eq_zero_of_eq_coord_mul (hU : IsOpen U) {f h : (ι → ℂ) → ℂ}
    (hf : HasLogGrowth S id U f) (hh : ContinuousOn h U) {k : ι}
    (he : ∀ z ∈ U, z ∉ coordDivisor S id → h z = z k * f z) {p : ι → ℂ} (hp : p ∈ U)
    (hk : p k = 0) : h p = 0 := by
  obtain ⟨K, hK, hpK, hKU⟩ := exists_compact_subset hU hp
  obtain ⟨C, N, hC, hb⟩ := hf.exists_one_le hKU hK
  set γ : ℂ → ι → ℂ := fun t j => if p j = 0 then t else p j with hγdef
  have hγ : Tendsto γ (𝓝[≠] 0) (𝓝 p) := (tendsto_ite_eq_zero_nhds_zero p).mono_left nhdsWithin_le_nhds
  obtain ⟨M, hM, key⟩ : ∃ M : ℝ, 1 ≤ M ∧
      ∀ t : ℂ, GlobalTheory.lwP₂ S (id (γ t)) ≤ M * (1 + |Real.log ‖t‖|) := by
    have hsum : 0 ≤ ∑ j ∈ S, |Real.log ‖p j‖| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    refine ⟨1 + ∑ j ∈ S, |Real.log ‖p j‖| + S.card, by linarith, fun t => ?_⟩
    have hs : ∑ j ∈ S, |Real.log ‖γ t j‖| ≤ ∑ j ∈ S, (|Real.log ‖p j‖| + |Real.log ‖t‖|) :=
      Finset.sum_le_sum fun j _ => by
        by_cases hj : p j = 0
        · simp only [hγdef, hj, if_true, norm_zero, Real.log_zero, abs_zero, zero_add, le_refl]
        · simp only [hγdef, hj, if_false]
          linarith [abs_nonneg (Real.log ‖t‖)]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
    have hL := abs_nonneg (Real.log ‖t‖)
    show 1 + ∑ j ∈ S, |Real.log ‖γ t j‖| ≤ _
    nlinarith [mul_nonneg hsum hL]
  have h1 : Tendsto (fun t => h (γ t)) (𝓝[≠] 0) (𝓝 (h p)) :=
    (hh.continuousAt (hU.mem_nhds hp)).tendsto.comp hγ
  have h2 : Tendsto (fun t => h (γ t)) (𝓝[≠] 0) (𝓝 0) := by
    have hφ := ((continuous_norm_mul_one_add_abs_log_pow N).tendsto' 0 0 (by simp)).const_mul
      (C * M ^ N)
    rw [mul_zero] at hφ
    refine squeeze_zero_norm' ?_ (hφ.mono_left nhdsWithin_le_nhds)
    filter_upwards [hγ (mem_interior_iff_mem_nhds.mp hpK), self_mem_nhdsWithin] with t htK ht0
    have hB : γ t ∉ coordDivisor S id := ite_eq_zero_notMem_coordDivisor S p ht0
    rw [he (γ t) (hKU htK) hB]
    have hk' : γ t k = t := by simp only [hγdef, hk, if_true]
    rw [hk', norm_mul]
    have hW0 : 0 ≤ GlobalTheory.lwP₂ S (id (γ t)) := (logWeight_pos _ _).le
    have hL := abs_nonneg (Real.log ‖t‖)
    have h3 : ‖f (γ t)‖ ≤ C * M ^ N * (1 + |Real.log ‖t‖|) ^ (N + 1) := by
      calc ‖f (γ t)‖ ≤ C * GlobalTheory.lwP₂ S (id (γ t)) ^ N := hb _ htK hB
        _ ≤ C * (M * (1 + |Real.log ‖t‖|)) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 (key t) N) (by linarith)
        _ = C * M ^ N * (1 + |Real.log ‖t‖|) ^ N := by rw [mul_pow, mul_assoc]
        _ ≤ C * M ^ N * (1 + |Real.log ‖t‖|) ^ (N + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.le_succ N))
              (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
    calc ‖t‖ * ‖f (γ t)‖ ≤ ‖t‖ * (C * M ^ N * (1 + |Real.log ‖t‖|) ^ (N + 1)) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = C * M ^ N * (‖t‖ * (1 + |Real.log ‖t‖|) ^ (N + 1)) := by ring
  exact tendsto_nhds_unique h1 h2

theorem exists_eq_coord_mul_of_isOpen (hU : IsOpen U) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (i : ι) (h0 : ∀ z ∈ U, z i = 0 → f z = 0) :
    ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, f z = z i * g z := by
  classical
  have loc : ∀ a ∈ U, a i = 0 → ∃ ε > 0, ∃ G : (ι → ℂ) → ℂ, Metric.ball a ε ⊆ U ∧
      DifferentiableOn ℂ G (Metric.ball a ε) ∧ ∀ z ∈ Metric.ball a ε, f z = z i * G z := by
    intro a ha hai
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU a ha
    have hpoly : (univ.pi fun _ : ι => Metric.ball (0 : ℂ) ε) = Metric.ball (0 : ι → ℂ) ε :=
      (ball_pi (0 : ι → ℂ) hε).symm
    have hmem : ∀ y ∈ Metric.ball (0 : ι → ℂ) ε, a + y ∈ Metric.ball a ε := by
      intro y hy
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hF : DifferentiableOn ℂ (fun y => f (a + y))
        (univ.pi fun _ : ι => Metric.ball (0 : ℂ) ε) := by
      rw [hpoly]
      exact hf.comp ((differentiableOn_const a).add differentiableOn_id) fun y hy => hball (hmem y hy)
    have hF0 : ∀ y ∈ univ.pi fun _ : ι => Metric.ball (0 : ℂ) ε, f (a + update y i 0) = 0 := by
      intro y hy
      have hy' : update y i 0 ∈ univ.pi fun _ : ι => Metric.ball (0 : ℂ) ε :=
        update_mem_polydisc hy (Metric.mem_ball_self hε)
      rw [hpoly] at hy'
      refine h0 _ (hball (hmem _ hy')) ?_
      simp [hai]
    obtain ⟨G, hG, hfG⟩ := exists_eq_coord_mul_of_vanishing hF i hF0
    refine ⟨ε, hε, fun z => G (z - a), hball, ?_, ?_⟩
    · rw [hpoly] at hG
      refine hG.comp (differentiableOn_id.sub (differentiableOn_const a)) fun z hz => ?_
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    · intro z hz
      have hz' : z - a ∈ univ.pi fun _ : ι => Metric.ball (0 : ℂ) ε := by
        rw [hpoly]; simpa [Metric.mem_ball, dist_eq_norm] using hz
      simpa [hai] using hfG (z - a) hz'
  let g : (ι → ℂ) → ℂ := fun z =>
    if z i = 0 then deriv (fun t => f (update z i t)) 0 else f z / z i
  have hgG : ∀ a ∈ U, a i = 0 → ∃ ε > 0, ∃ G : (ι → ℂ) → ℂ,
      DifferentiableOn ℂ G (Metric.ball a ε) ∧ ∀ z ∈ Metric.ball a ε, g z = G z := by
    intro a ha hai
    obtain ⟨ε, hε, G, -, hG, hfG⟩ := loc a ha hai
    refine ⟨ε, hε, G, hG, fun z hz => ?_⟩
    by_cases hzi : z i = 0
    · simp only [g, hzi, if_true]
      have hGz : DifferentiableAt ℂ G z := hG.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
      have hu : HasDerivAt (update z i) (Pi.single i (1 : ℂ)) 0 := hasDerivAt_update z i 0
      have hz0 : update z i 0 = z := by rw [← hzi]; exact update_eq_self i z
      have hGz' : HasFDerivAt G (fderiv ℂ G z) (update z i 0) := by
        rw [hz0]; exact hGz.hasFDerivAt
      have hk : HasDerivAt (fun t => G (update z i t)) (fderiv ℂ G z (Pi.single i 1)) 0 :=
        hGz'.comp_hasDerivAt 0 hu
      have hprod : HasDerivAt (fun t => t * G (update z i t))
          (1 * G (update z i 0) + 0 * fderiv ℂ G z (Pi.single i 1)) 0 :=
        (hasDerivAt_id' (0 : ℂ)).mul hk
      have hev : (fun t => f (update z i t)) =ᶠ[𝓝 0] fun t => t * G (update z i t) := by
        have hm : update z i ⁻¹' Metric.ball a ε ∈ 𝓝 (0 : ℂ) :=
          hu.continuousAt.preimage_mem_nhds (by rw [hz0]; exact Metric.isOpen_ball.mem_nhds hz)
        filter_upwards [hm] with t ht
        rw [hfG _ ht]
        simp
      rw [hev.deriv_eq, hprod.deriv]
      simp [hz0]
    · simp only [g, hzi, if_false]
      rw [hfG z hz]
      field_simp
  refine ⟨g, ?_, ?_⟩
  · intro a ha
    by_cases hai : a i = 0
    · obtain ⟨ε, hε, G, hG, hgG'⟩ := hgG a ha hai
      have hGa : DifferentiableAt ℂ G a := hG.differentiableAt (Metric.ball_mem_nhds a hε)
      have hev : g =ᶠ[𝓝 a] G := Filter.eventually_of_mem (Metric.ball_mem_nhds a hε) hgG'
      exact (hGa.congr_of_eventuallyEq hev).differentiableWithinAt
    · have hne : ∀ᶠ z in 𝓝 a, z i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hai
      have hfa : DifferentiableAt ℂ f a := hf.differentiableAt (hU.mem_nhds ha)
      have hci : DifferentiableAt ℂ (fun z : ι → ℂ => z i) a := by fun_prop
      have hq : DifferentiableAt ℂ (fun z => f z * (z i)⁻¹) a := hfa.mul (hci.inv hai)
      have hev : g =ᶠ[𝓝 a] fun z => f z * (z i)⁻¹ := hne.mono fun z hz => by
        simp only [g, hz, if_false, div_eq_mul_inv]
      exact (hq.congr_of_eventuallyEq hev).differentiableWithinAt
  · intro z hz
    by_cases hzi : z i = 0
    · rw [h0 z hz hzi, hzi, zero_mul]
    · simp only [g, hzi, if_false]
      field_simp

theorem HasLogGrowth.exists_extension_of_prod_mul (hU : IsOpen U) {f : (ι → ℂ) → ℂ}
    (hf : HasLogGrowth S id U f) (l : List ι) (hl : ∀ j ∈ l, j ∈ S) :
    ∀ h : (ι → ℂ) → ℂ, DifferentiableOn ℂ h U →
      (∀ z ∈ U, z ∉ coordDivisor S id → h z = (l.map z).prod * f z) →
      ∃ f' : (ι → ℂ) → ℂ, DifferentiableOn ℂ f' U ∧ Set.EqOn f' f (U \ coordDivisor S id) := by
  induction l with
  | nil =>
    intro h hh he
    refine ⟨h, hh, fun z hz => ?_⟩
    simpa using he z hz.1 hz.2
  | cons j l ih =>
    intro h hh he
    have hjS : j ∈ S := hl j (by simp)
    have hlS : ∀ i ∈ l, i ∈ S := fun i hi => hl i (by simp [hi])
    have hq : HasLogGrowth S id U fun z => (l.map z).prod * f z :=
      (HasLogGrowth.of_continuousOn
        (continuous_list_prod l fun i _ => continuous_apply i).continuousOn).mul hf
    have hvan : ∀ z ∈ U, z j = 0 → h z = 0 := fun z hz hzj =>
      hq.eq_zero_of_eq_coord_mul hU hh.continuousOn
        (fun y hy hyB => by
          rw [he y hy hyB, List.map_cons, List.prod_cons, mul_assoc]) hz hzj
    obtain ⟨g, hg, hhg⟩ := exists_eq_coord_mul_of_isOpen hU hh j hvan
    refine ih hlS g hg fun z hz hzB => ?_
    have hzj : z j ≠ 0 := (notMem_coordDivisor.mp hzB) j hjS
    have := he z hz hzB
    rw [hhg z hz, List.map_cons, List.prod_cons, mul_assoc] at this
    exact mul_left_cancel₀ hzj this

end

theorem HasLogGrowth.exists_differentiableOn_extension {ι : Type*} [Fintype ι]
    {S : Finset ι} {U : Set (ι → ℂ)} (hU : IsOpen U) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (U \ coordDivisor S id)) (hg : HasLogGrowth S id U f) :
    ∃ f' : (ι → ℂ) → ℂ, DifferentiableOn ℂ f' U ∧ Set.EqOn f' f (U \ coordDivisor S id) := by
  classical
  have hBc : IsClosed (coordDivisor S (id : (ι → ℂ) → ι → ℂ)) :=
    isClosed_coordDivisor S fun j _ => continuous_apply j
  obtain ⟨P, hP⟩ : ∃ P : (ι → ℂ) → ℂ, P = fun z => ∏ j ∈ S, z j := ⟨_, rfl⟩
  have hPd : ∀ z, DifferentiableAt ℂ P z := by
    intro z; rw [hP]; fun_prop
  have hh : DifferentiableOn ℂ (fun z => P z * (P z * f z)) U := by
    intro p hp
    by_cases hpB : p ∈ coordDivisor S id
    · have hP0 : P p = 0 := by rw [hP]; exact mem_coordDivisor_iff_prod_eq_zero.mp hpB
      have ht := hg.tendsto_prod_mul hU hp hpB fun j _ => (continuous_apply j).continuousAt
      have ho : Asymptotics.IsLittleO (nhds p) (fun z => P z * f z) (fun _ => (1 : ℝ)) := by
        rw [Asymptotics.isLittleO_one_iff, hP]; exact ht
      have hfd : HasFDerivAt (fun z => P z * (P z * f z)) (0 : (ι → ℂ) →L[ℂ] ℂ) p := by
        rw [hasFDerivAt_iff_isLittleO]
        refine Asymptotics.isLittleO_norm_right.mp ?_
        refine ((hPd p).isBigO_sub.norm_right.mul_isLittleO ho).congr (fun z => ?_)
          (fun z => mul_one _)
        simp [hP0]
      exact hfd.differentiableAt.differentiableWithinAt
    · have hpUB : U \ coordDivisor S id ∈ nhds p := (hU.sdiff hBc).mem_nhds ⟨hp, hpB⟩
      have hfd : DifferentiableAt ℂ f p := hf.differentiableAt hpUB
      exact ((hPd p).mul ((hPd p).mul hfd)).differentiableWithinAt
  have hl : ∀ j ∈ S.toList ++ S.toList, j ∈ S := fun j hj => by simpa using hj
  refine hg.exists_extension_of_prod_mul hU (S.toList ++ S.toList) hl _ hh fun z _ _ => ?_
  rw [List.map_append, List.prod_append, Finset.prod_map_toList]
  simp only [hP]
  ring

end GlobalTheory
