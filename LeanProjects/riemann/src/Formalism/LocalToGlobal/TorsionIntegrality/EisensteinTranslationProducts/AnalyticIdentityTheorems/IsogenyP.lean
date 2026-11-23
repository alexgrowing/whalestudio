import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace IsogenyPAux

lemma P_local (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice) (w : ℂ) :
    L.weierstrassP w = L.weierstrassPExcept 0 (w - ω) + 1 / (w - ω) ^ 2 := by
  have h1 := L.weierstrassPExcept_add (0 : L.lattice) (w - ω)
  have h2 := L.weierstrassP_sub_coe w ⟨ω, hω⟩
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h1 h2
  rw [← h2, ← h1]

lemma analyticAt_P (L : PeriodPair) (a b z : ℂ) (hz : a * z + b ∉ L.lattice) :
    AnalyticAt ℂ (fun w => L.weierstrassP (a * w + b)) z :=
  AnalyticAt.fun_comp (f := fun w : ℂ => a * w + b) (g := L.weierstrassP)
    (L.analyticOnNhd_weierstrassP _ hz) (by fun_prop)

lemma analyticAt_PExcept (L : PeriodPair) (a z : ℂ) :
    AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (a * (w - z))) z := by
  refine AnalyticAt.fun_comp (f := fun w : ℂ => a * (w - z)) (g := L.weierstrassPExcept 0) ?_
    (by fun_prop)
  simpa using L.analyticAt_weierstrassPExcept 0

lemma eventually_notMem (L : PeriodPair) (α z : ℂ) (hα : α ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, α * w ∉ L.lattice := by
  have h1 : ∀ᶠ w in 𝓝 z, α * w ∈ ((L.lattice : Set ℂ) \ {α * z})ᶜ :=
    ((continuous_const.mul continuous_id).tendsto z).eventually
      (L.compl_lattice_sdiff_singleton_mem_nhds (α * z))
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hne hmem
  refine hw ⟨hmem, ?_⟩
  simpa [hα] using hne

lemma ext_at (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α)
    (h1 : ∀ P ∈ T, α * P ∈ L.lattice)
    (h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q)
    (z₀ P' : ℂ) (hP' : P' ∈ T) (hz : z₀ + P' ∈ L.lattice) :
    AnalyticAt ℂ (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) z₀ ∧
    (fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P)) =ᶠ[𝓝[≠] z₀]
      (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) := by
  constructor
  · refine ((analyticAt_const.mul (analyticAt_PExcept L α z₀)).sub (analyticAt_PExcept L 1 z₀)).sub ?_
    refine Finset.analyticAt_fun_sum _ fun P hP => analyticAt_P L 1 P z₀ ?_
    intro hmem
    rw [one_mul] at hmem
    refine (Finset.mem_erase.1 hP).1 (h2 P (Finset.mem_erase.1 hP).2 P' hP' ?_)
    have := L.lattice.sub_mem hmem hz
    simpa using this
  · have hαz : α * z₀ ∈ L.lattice := by
      have := L.lattice.sub_mem (hst _ hz) (h1 P' hP')
      have e : α * (z₀ + P') - α * P' = α * z₀ := by ring
      rwa [e] at this
    filter_upwards [self_mem_nhdsWithin] with w hne
    have hne' : w - z₀ ≠ 0 := sub_ne_zero.2 hne
    rw [← Finset.add_sum_erase T _ hP', P_local L (α * z₀) hαz (α * w),
      P_local L (z₀ + P') hz (w + P')]
    have e1 : α * w - α * z₀ = α * (w - z₀) := by ring
    have e2 : w + P' - (z₀ + P') = w - z₀ := by ring
    rw [e1, e2]
    simp only [one_mul]
    field_simp
    ring

end IsogenyPAux

open IsogenyPAux

theorem isogenyWeierstrassP_of_ellipticNoPole (hN : EllipticNoPole) : IsogenyP := by
  intro L α S hα hst hS z hz
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have h0S : (0 : ℂ) ∉ S := fun h => (hS1 0 h).2 L.lattice.zero_mem
  set T : Finset ℂ := insert 0 S with hT
  have h1 : ∀ P ∈ T, α * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · simp
    · exact (hS1 P hP).1
  have h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_insert.1 hP with rfl | hP <;> rcases Finset.mem_insert.1 hQ with rfl | hQ
    · rfl
    · exact absurd (by simpa using hPQ) (hS1 Q hQ).2
    · exact absurd (by simpa using hPQ) (hS1 P hP).2
    · exact hS2 P hP Q hQ hPQ
  have h3 : ∀ z₀, α * z₀ ∈ L.lattice → ∃ P ∈ T, z₀ + P ∈ L.lattice := by
    intro z₀ hz₀
    by_cases hm : z₀ ∈ L.lattice
    · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
    · obtain ⟨P, hP, hPz⟩ := hS3 (-z₀) (by simpa using L.lattice.neg_mem hz₀)
        (fun h => hm (by simpa using L.lattice.neg_mem h))
      refine ⟨P, Finset.mem_insert_of_mem hP, ?_⟩
      have := L.lattice.neg_mem hPz
      have e : -(-z₀ - P) = z₀ + P := by ring
      rwa [e] at this
  set f : ℂ → ℂ := fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P) with hf

  have han : ∀ z₀, α * z₀ ∉ L.lattice → AnalyticAt ℂ f z₀ := by
    intro z₀ hz₀
    have a1 : AnalyticAt ℂ (fun w => L.weierstrassP (α * w)) z₀ := by
      simpa using analyticAt_P L α 0 z₀ (by simpa using hz₀)
    refine (analyticAt_const.mul a1).sub (Finset.analyticAt_fun_sum _ fun P hP => ?_)
    have := analyticAt_P L 1 P z₀ (by
      intro hmem
      rw [one_mul] at hmem
      apply hz₀
      have := L.lattice.sub_mem (hst _ hmem) (h1 P hP)
      have e : α * (z₀ + P) - α * P = α * z₀ := by ring
      rwa [e] at this)
    simpa using this
  have hext : ∀ z₀, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
    intro z₀
    by_cases hz₀ : α * z₀ ∈ L.lattice
    · obtain ⟨P', hP', hzP⟩ := h3 z₀ hz₀
      exact ⟨_, ext_at L α T hα hst h1 h2 z₀ P' hP' hzP⟩
    · exact ⟨f, han z₀ hz₀, EventuallyEq.rfl⟩
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    obtain ⟨g, hg, hfg⟩ := hext z
    exact hg.meromorphicAt.congr hfg.symm
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := fun z =>
    (hmer z).meromorphicOrderAt_nonneg_iff.2 (hext z)
  have hper : IsPeriodic L f := by
    intro ω hω w
    simp only [hf]
    have e1 : α * (w + ω) = α * w + α * ω := by ring
    rw [e1, L.weierstrassP_add_coe (α * w) ⟨α * ω, hst ω hω⟩]
    congr 1
    refine Finset.sum_congr rfl fun P _ => ?_
    have e2 : w + ω + P = w + P + ω := by ring
    rw [e2, L.weierstrassP_add_coe (w + P) ⟨ω, hω⟩]
  obtain ⟨c, hc⟩ := hN L f hmer hper hord

  have hc0 : c = -∑ P ∈ S, L.weierstrassP P := by
    obtain ⟨ha, he⟩ := ext_at L α T hα hst h1 h2 0 0 (Finset.mem_insert_self _ _) (by simp)
    have hev : (fun _ : ℂ => c) =ᶠ[𝓝[≠] 0] f := by
      filter_upwards [eventually_notMem L α 0 hα] with w hw
      exact (hc w (han w hw).continuousAt).symm
    have := Elliptic.eq_of_eventuallyEq_nhdsNE continuousAt_const ha.continuousAt (hev.trans he)
    rw [this, hT, Finset.erase_insert h0S]
    simp
  have hfz := hc z (han z hz).continuousAt
  rw [hc0] at hfz
  simp only [hf, hT, Finset.sum_insert h0S, add_zero] at hfz
  rw [Finset.sum_sub_distrib]
  linear_combination hfz

theorem isogeny_weierstrass_p : IsogenyP := isogenyWeierstrassP_of_ellipticNoPole elliptic_no_pole_const

end Formalism.L2.Th1.F
