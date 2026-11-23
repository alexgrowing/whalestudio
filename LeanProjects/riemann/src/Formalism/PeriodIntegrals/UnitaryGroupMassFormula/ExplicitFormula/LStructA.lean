import Mathlib

noncomputable section

namespace PI.EF

open Complex Filter Topology Set

lemma logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s := by
  have hn : analyticOrderAt f ρ = (analyticOrderNatAt f ρ : ℕ∞) := (Nat.cast_analyticOrderNatAt hfin).symm
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast).1 hn
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have hU : ∀ᶠ z in 𝓝 ρ, (∀ᶠ w in 𝓝 z, f w = (w - ρ) ^ analyticOrderNatAt f ρ • g w) ∧
      g z ≠ 0 ∧ AnalyticAt ℂ g z :=
    hfg.eventually_nhds.and ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs hsne
  obtain ⟨hfs, hgs, hga⟩ := hs
  have hsr : s - ρ ≠ 0 := sub_ne_zero.2 hsne
  have hpow : (s - ρ) ^ analyticOrderNatAt f ρ ≠ 0 := pow_ne_zero _ hsr
  have hfs' : f s = (s - ρ) ^ analyticOrderNatAt f ρ * g s := by rw [hfs.self_of_nhds, smul_eq_mul]
  refine ⟨by rw [hfs']; exact mul_ne_zero hpow hgs, ?_⟩
  have hd : DifferentiableAt ℂ (fun w : ℂ => w - ρ) s := differentiableAt_id.sub_const ρ
  have hld : logDeriv f s = logDeriv (fun w => (w - ρ) ^ analyticOrderNatAt f ρ * g w) s := by
    rw [logDeriv_apply, logDeriv_apply,
      Filter.EventuallyEq.deriv_eq (hfs.mono fun w hw => by rw [hw, smul_eq_mul]), hfs']
  have hl : logDeriv (fun w : ℂ => w - ρ) s = 1 / (s - ρ) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  rw [hld, logDeriv_mul (f := fun w => (w - ρ) ^ analyticOrderNatAt f ρ) s hpow hgs (hd.pow _)
    hga.differentiableAt, logDeriv_fun_pow hd, hl, logDeriv_apply]
  beta_reduce
  ring

theorem exists_regular_part {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K) (Z : Finset ℂ)
    (hZ0 : ∀ ρ ∈ Z, f ρ = 0) (hK : ∀ s ∈ K, f s = 0 → s ∈ Z)
    (hfin : ∀ ρ ∈ K, analyticOrderAt f ρ ≠ ⊤) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H K ∧ ∀ s ∈ K, f s ≠ 0 →
      logDeriv f s = H s + ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
  classical
  have hloc : ∀ ρ, ρ ∈ K → ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s :=
    fun ρ hρ => logDeriv_local (hf ρ hρ) (hfin ρ hρ)
  choose! k hk hkev using hloc
  have hsumA : ∀ (W : Finset ℂ) (s0 : ℂ), s0 ∉ W →
      AnalyticAt ℂ (fun s => ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
    intro W s0 hW
    have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := s0) W
      (f := fun ρ (s : ℂ) => (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
      (fun ρ hρ => analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.2 fun h => hW (h ▸ hρ)))
    convert h using 1
    ext s
    simp [Finset.sum_apply]
  let H : ℂ → ℂ := fun s => if s ∈ Z ∧ s ∈ K then
      k s s - ∑ ρ ∈ Z.erase s, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
    else logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
  refine ⟨H, ?_, ?_⟩
  · intro s0 hs0
    by_cases hz : s0 ∈ Z
    · have hRa : AnalyticAt ℂ
          (fun s => k s0 s - ∑ ρ ∈ Z.erase s0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 :=
        (hk s0 hs0).sub (hsumA _ s0 (by simp))
      have h1 := hkev s0 hs0
      rw [eventually_nhdsWithin_iff] at h1
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z.erase s0 :=
        (Z.erase s0).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine hRa.congr ?_
      filter_upwards [h1, h2] with s hs1 hs2
      by_cases hss : s = s0
      · subst hss
        simp only [H, if_pos (And.intro hz hs0)]
      · have hsZ : s ∉ Z := fun h => hs2 (Finset.mem_erase.2 ⟨hss, h⟩)
        obtain ⟨_, hl⟩ := hs1 hss
        simp only [H, hsZ, false_and, if_false]
        rw [hl, ← Finset.add_sum_erase Z _ hz]
        ring
    · have hf0 : f s0 ≠ 0 := fun h => hz (hK s0 hs0 h)
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z :=
        Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hz)
      have hA : AnalyticAt ℂ (fun s => logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
        refine AnalyticAt.sub ?_ (hsumA Z s0 hz)
        have e : logDeriv f = fun s => deriv f s / f s := funext fun s => logDeriv_apply f s
        rw [e]
        exact (hf s0 hs0).deriv.div (hf s0 hs0) hf0
      refine hA.congr ?_
      filter_upwards [h2] with s hs
      simp only [H, hs, false_and, if_false]
  · intro s _ hfs
    have hsZ : s ∉ Z := fun h => hfs (hZ0 s h)
    simp only [H, hsZ, false_and, if_false]
    ring

lemma finite_zeros_of_compact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by
  by_contra hinf
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK Set.inter_subset_left
  have hfr : ∃ᶠ w in 𝓝[≠] z, f w = 0 := by
    rw [accPt_iff_frequently] at hacc
    rw [Filter.Frequently, eventually_nhdsWithin_iff]
    intro h
    apply hacc
    filter_upwards [h] with w hw
    rintro ⟨hne, hw'⟩
    exact hw hne hw'.2
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ z) hfr
  exact hx (h0 (Set.mem_univ x))

lemma order_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (y : ℂ) : analyticOrderAt f y ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ y) htop
  exact hx (h0 (Set.mem_univ x))

end PI.EF
