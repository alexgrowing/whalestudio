import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

private theorem closedBall_mem_nhds_of_mem_closedBall_lt {z₀ z : ℂ} {r R₁ : ℝ} (hR : R₁ < r)
    (hz : z ∈ Metric.closedBall z₀ R₁) : Metric.closedBall z₀ r ∈ 𝓝 z :=
  Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hR hz))
    Metric.ball_subset_closedBall

private theorem natCast_analyticOrderNatAt_of_ne_top {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderAt f z ≠ ⊤) : ((analyticOrderNatAt f z : ℕ) : ℕ∞) = analyticOrderAt f z :=
  ENat.natCast_toNat h

theorem exists_factorization_of_sum_order (z₀ : ℂ) (r R₁ : ℝ) (hR : R₁ < r) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (Metric.closedBall z₀ r) →
      (∀ ρ ∈ Z, ρ ∈ Metric.closedBall z₀ R₁) →
      (∀ z ∈ Metric.closedBall z₀ R₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
        (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
        ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  classical
  intro N
  induction N with
  | zero =>
    intro f Z hf hZ hzero htop hsum
    have h0 : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = 0 := Finset.sum_eq_zero_iff.mp hsum
    refine ⟨f, hf, ?_, ?_⟩
    · intro z hz hfz
      have hzZ := hzero z hz hfz
      have han : AnalyticAt ℂ f z := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hz)
      have hord : analyticOrderAt f z = 0 := by
        rw [← natCast_analyticOrderNatAt_of_ne_top (htop z hzZ)]
        simp [h0 z hzZ]
      exact (han.analyticOrderAt_eq_zero.mp hord) hfz
    · intro z _
      rw [Finset.prod_eq_one (fun ρ hρ => by rw [h0 ρ hρ, pow_zero]), one_mul]
  | succ n ih =>
    intro f Z hf hZ hzero htop hsum
    obtain ⟨ρ₀, hρ₀Z, hρ₀⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact Nat.succ_ne_zero n)
    have hρ₀B := hZ ρ₀ hρ₀Z
    have hanρ₀ : AnalyticAt ℂ f ρ₀ := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)
    have hfρ₀ : f ρ₀ = 0 := by
      by_contra hne
      apply hρ₀
      have h0 : analyticOrderAt f ρ₀ = 0 := hanρ₀.analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, h0]
    obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = dslope f ρ₀ := ⟨_, rfl⟩
    have hfg : ∀ z, f z = (z - ρ₀) * g z := by
      intro z
      have h := sub_smul_dslope f ρ₀ z
      rw [hfρ₀, sub_zero, smul_eq_mul, ← hg] at h
      exact h.symm
    have hgd : DifferentiableOn ℂ g (Metric.closedBall z₀ r) := by
      rw [hg]
      exact (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)).mpr hf
    have hfeq : f = (fun z : ℂ => z - ρ₀) * g := funext fun z => hfg z
    have key : ∀ ρ ∈ Z,
        analyticOrderAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderAt g ρ := by
      intro ρ hρ
      have hB := hZ ρ hρ
      have hga : AnalyticAt ℂ g ρ := hgd.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hB)
      have hla : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ := analyticAt_id.sub analyticAt_const
      rw [hfeq, analyticOrderAt_mul hla hga]
      congr 1
      split_ifs with hρρ₀
      · rw [hρρ₀]
        have hl : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ₀ := analyticAt_id.sub analyticAt_const
        have h1 := (hl.analyticOrderAt_eq_natCast (n := 1)).mpr
          ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => by simp⟩
        simpa using h1
      · exact hla.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρρ₀)
    have keyN : ∀ ρ ∈ Z,
        analyticOrderNatAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ ∧
          analyticOrderAt g ρ ≠ ⊤ := by
      intro ρ hρ
      have hk := key ρ hρ
      have ht := htop ρ hρ
      have hgt : analyticOrderAt g ρ ≠ ⊤ := by
        intro h
        apply ht
        rw [hk, h]
        simp
      refine ⟨?_, hgt⟩
      have h1 : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) =
          (((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ : ℕ) : ℕ∞) := by
        rw [natCast_analyticOrderNatAt_of_ne_top ht, hk, Nat.cast_add,
          natCast_analyticOrderNatAt_of_ne_top hgt]
        split_ifs <;> simp
      exact_mod_cast h1
    have hsumg : ∑ ρ ∈ Z, analyticOrderNatAt g ρ = n := by
      have hs : ∑ ρ ∈ Z, analyticOrderNatAt f ρ =
          ∑ ρ ∈ Z, ((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ) :=
        Finset.sum_congr rfl fun ρ hρ => (keyN ρ hρ).1
      rw [hs, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_ite_eq', hρ₀Z, if_true] at hsum
      omega
    have hzg : ∀ z ∈ Metric.closedBall z₀ R₁, g z = 0 → z ∈ Z :=
      fun z hz h0 => hzero z hz (by rw [hfg z, h0, mul_zero])
    obtain ⟨h, hhd, hh0, hhf⟩ := ih g Z hgd hZ hzg (fun ρ hρ => (keyN ρ hρ).2) hsumg
    refine ⟨h, hhd, hh0, fun z hz => ?_⟩
    have hone : ∏ ρ ∈ Z, (z - ρ) ^ (if ρ = ρ₀ then 1 else 0) = z - ρ₀ := by
      rw [Finset.prod_eq_single ρ₀ (fun b _ hb => by simp [hb]) (fun h => absurd hρ₀Z h)]
      simp
    have hprod : ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ =
        (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
      calc ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ
          = ∏ ρ ∈ Z, ((z - ρ) ^ (if ρ = ρ₀ then 1 else 0) * (z - ρ) ^ analyticOrderNatAt g ρ) :=
            Finset.prod_congr rfl fun ρ hρ => by rw [(keyN ρ hρ).1, pow_add]
        _ = (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
            rw [Finset.prod_mul_distrib, hone]
    rw [hfg z, hhf z hz, hprod, mul_assoc]

theorem zeroFactorization : ZeroFactor := by
  intro f z₀ r R₁ hR₁ hR hf hf0
  have hr : 0 < r := hR₁.trans hR
  have hU : AnalyticOnNhd ℂ f (Metric.ball z₀ r) :=
    (hf.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hpre : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have hnotzero : ∀ x ∈ Metric.ball z₀ r, ¬ (∀ᶠ w in 𝓝 x, f w = 0) := by
    intro x hx hev
    have hEq := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx hev
    exact hf0 (hEq hz₀)
  have hisol : ∀ x ∈ Metric.ball z₀ r, ∀ᶠ w in 𝓝[≠] x, f w ≠ 0 := fun x hx =>
    ((hU x hx).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hnotzero x hx)
  have htop : ∀ x ∈ Metric.ball z₀ r, analyticOrderAt f x ≠ ⊤ := fun x hx h =>
    hnotzero x hx (analyticOrderAt_eq_top.mp h)
  have hSsub : Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} ⊆ Metric.ball z₀ r :=
    fun x hx => Metric.closedBall_subset_ball hR hx.1
  have hScpt : IsCompact (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}) :=
    (isCompact_closedBall z₀ R₁).of_isClosed_subset
      ((hf.continuousOn.mono (Metric.closedBall_subset_closedBall hR.le)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall isClosed_singleton)
      Set.inter_subset_left
  have hSdisc : DiscreteTopology (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} : Set ℂ) := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    refine Filter.inf_principal_eq_bot.mpr ?_
    filter_upwards [hisol x (hSsub hx)] with w hw hwS
    exact hw hwS.2
  have hfin : (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}).Finite := by
    exact hScpt.finite ⟨hSdisc⟩
  have hmem : ∀ ρ : ℂ, ρ ∈ hfin.toFinset ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0) := by
    intro ρ
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨h, hhd, hh0, hhf⟩ := exists_factorization_of_sum_order z₀ r R₁ hR _ f hfin.toFinset hf
    (fun ρ hρ => ((hmem ρ).mp hρ).1) (fun z hz hfz => (hmem z).mpr ⟨hz, hfz⟩)
    (fun ρ hρ => htop ρ (Metric.closedBall_subset_ball hR ((hmem ρ).mp hρ).1)) rfl
  refine ⟨hfin.toFinset, analyticOrderNatAt f, h, hmem, ?_, hhd, hh0, hhf⟩
  intro ρ hρ
  obtain ⟨hB, hfρ⟩ := (hmem ρ).mp hρ
  have hball : ρ ∈ Metric.ball z₀ r := Metric.closedBall_subset_ball hR hB
  have hne : analyticOrderAt f ρ ≠ 0 := fun h0 =>
    ((hU ρ hball).analyticOrderAt_eq_zero.mp h0) hfρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← natCast_analyticOrderNatAt_of_ne_top (htop ρ hball)]
  simp [h0]

end Formalism.ZF
