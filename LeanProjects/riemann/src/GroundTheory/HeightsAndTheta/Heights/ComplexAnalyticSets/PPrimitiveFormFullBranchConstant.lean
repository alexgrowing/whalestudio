import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormFullBranchConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem monic_root_branch_eventuallyEq {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (s : Fin d → ℂ)
    (u v : (Fin d → ℂ) → ℂ) (ha : ∀ j, ContinuousAt (a j) s) (hu : ContinuousAt u s)
    (hv : ContinuousAt v s) (huv : u s = v s)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hru : ∀ᶠ t in 𝓝 s, u t ^ N + ∑ j, a j t * u t ^ (j : ℕ) = 0)
    (hrv : ∀ᶠ t in 𝓝 s, v t ^ N + ∑ j, a j t * v t ^ (j : ℕ) = 0) : u =ᶠ[𝓝 s] v := by
  set Q : (Fin d → ℂ) → ℂ → ℂ → ℂ := fun t x y =>
    ∑ i ∈ Finset.range N, x ^ i * y ^ (N - 1 - i) +
      ∑ j : Fin N, a j t * ∑ i ∈ Finset.range j, x ^ i * y ^ ((j : ℕ) - 1 - i) with hQdef
  have hQ : ∀ t x y, (x ^ N + ∑ j, a j t * x ^ (j : ℕ)) - (y ^ N + ∑ j, a j t * y ^ (j : ℕ)) =
      Q t x y * (x - y) := by
    intro t x y
    rw [hQdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hQs : Q s (u s) (u s) ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := u s)
      (by simpa [Polynomial.eval₂_id, Polynomial.eval_finsetSum] using hru.self_of_nhds)
    convert h using 1
    simp [hQdef, Polynomial.eval₂_id, Polynomial.eval_finsetSum, geom_sum₂_self, Polynomial.derivative_X_pow]
  have hc : ContinuousAt (fun t => Q t (u t) (v t)) s := by
    simp only [hQdef]
    fun_prop
  have hne : ∀ᶠ t in 𝓝 s, Q t (u t) (v t) ≠ 0 := hc.eventually_ne (by rw [← huv]; exact hQs)
  filter_upwards [hru, hrv, hne] with t h1 h2 h3
  have h := hQ t (u t) (v t)
  rw [h1, h2, sub_self] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left h3)

theorem PrimitiveFormFullBranchConstant.proof : PrimitiveFormFullBranchConstant.Statement := by
  intro σ _ X W N' k f d A ℓ N a δ q B O r hW hN' hWN' hf hXN' hXW hP hB ha hδ hq hO hOc hOB hδO hsep hr hrO
  set G : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hGdef
  set P : (Fin d → ℂ) → Prop := fun u => G u ∈ X ∩ W ∧ A (G u) = u ∧ ℓ (G u) = r u with hPdef
  have hG : AnalyticOnNhd ℂ G O := fun u hu => analyticAt_pi_iff.2 fun i =>
    (Finset.analyticAt_fun_sum _ fun j _ => (hq i j u (hOB hu)).mul ((hr u hu).pow _)).div
      (hδ u (hOB hu)) (hδO u hu)

  have hfull : ∀ s ∈ O, (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ ∀ᶠ u in 𝓝 s, P u) := by
    intro s hs
    constructor
    · rintro ⟨O', r', hO', hsO', hr', hrs, hw⟩
      have hroot' : ∀ᶠ u in 𝓝 s, r' u ^ N + ∑ j, a j u * r' u ^ (j : ℕ) = 0 := by
        filter_upwards [hO'.mem_nhds hsO'] with u hu
        obtain ⟨hX, hA, hℓ⟩ := hw u hu
        have h := hP _ hX
        rwa [hA, hℓ] at h
      have heq : r' =ᶠ[𝓝 s] r := monic_root_branch_eventuallyEq a s r' r
        (fun j => (ha j s (hOB hs)).continuousAt) (hr' s hsO').continuousAt (hr s hs).continuousAt hrs
        (hsep s hs) hroot' (Filter.mem_of_superset (hO.mem_nhds hs) hrO)
      filter_upwards [hO'.mem_nhds hsO', heq] with u hu hru
      have h := hw u hu
      simp only [hru] at h
      exact h
    · intro hev
      obtain ⟨U, hUs, hUo, hsU⟩ := mem_nhds_iff.1 hev
      exact ⟨U ∩ O, r, hUo.inter hO, ⟨hsU, hs⟩, hr.mono Set.inter_subset_right, rfl, fun u hu => hUs hu.1⟩

  set S : Set (Fin d → ℂ) := {s | ∀ᶠ u in 𝓝 s, P u} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : closure S ∩ O ⊆ S := by
    rintro s ⟨hsc, hs⟩
    have hGs : ContinuousAt G s := (hG s hs).continuousAt
    have hGW : G s ∈ closure W := closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hu.self_of_nhds.1.2)
      (mem_closure_image hGs hsc)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      (Filter.inter_mem (hO.mem_nhds hs) (hGs.preimage_mem_nhds (hN'.mem_nhds (hWN' hGW))))

    set Φ : (Fin d → ℂ) → (Fin k → ℂ) × (Fin d → ℂ) × ℂ :=
      fun u => (fun i => f i (G u), A (G u) - u, ℓ (G u) - r u) with hΦdef
    have hΦ : AnalyticOnNhd ℂ Φ (Metric.ball s ε) := fun u hu => by
      have hu' := hball hu
      exact (analyticAt_pi_iff.2 fun i => (hf i _ hu'.2).comp (hG u hu'.1)).prod
        ((((A.analyticAt _).comp (hG u hu'.1)).sub analyticAt_id).prod
          (((ℓ.analyticAt _).comp (hG u hu'.1)).sub (hr u hu'.1)))
    obtain ⟨u₀, hu₀U, hu₀S⟩ := mem_closure_iff.1 hsc _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hΦ0 : Set.EqOn Φ 0 (Metric.ball s ε) :=
      hΦ.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball s ε).isPreconnected hu₀U (by
        filter_upwards [hu₀S] with u hu
        obtain ⟨⟨hX, hWu⟩, hA, hℓ⟩ := hu
        have hXN : G u ∈ X ∩ N' := ⟨hX, hWN' (subset_closure hWu)⟩
        rw [hXN'] at hXN
        simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, hA, hℓ, sub_self, and_true]
        exact funext fun i => hXN.2 i)
    have hU : ∀ u ∈ Metric.ball s ε, G u ∈ X ∧ A (G u) = u ∧ ℓ (G u) = r u := by
      intro u hu
      have h := hΦ0 hu
      simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, sub_eq_zero] at h
      refine ⟨?_, h.2.1, h.2.2⟩
      have hXN : G u ∈ X ∩ N' := by rw [hXN']; exact ⟨(hball hu).2, fun i => congr_fun h.1 i⟩
      exact hXN.1
    obtain ⟨hXs, hAs, -⟩ := hU s (Metric.mem_ball_self hε)
    have hGsW : G s ∈ W := hXW _ ⟨hXs, hGW⟩ (by rw [hAs]; exact hOB hs)
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε),
      hGs.preimage_mem_nhds (hW.mem_nhds hGsW)] with u hu hu'
    obtain ⟨h1, h2, h3⟩ := hU u hu
    exact ⟨⟨h1, hu'⟩, h2, h3⟩

  have key : ∀ s ∈ O, ∀ s' ∈ O, PrimitiveFormRootFull X W A ℓ δ q s (r s) →
      PrimitiveFormRootFull X W A ℓ δ q s' (r s') := by
    intro s hs s' hs' h
    have hsub : O ⊆ S := hOc.subset_of_closure_inter_subset hSo ⟨s, hs, (hfull s hs).1 h⟩ hSc
    exact (hfull s' hs').2 (hsub hs')
  intro s hs s' hs'
  exact ⟨key s hs s' hs', key s' hs' s hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
