import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology Metric Set

noncomputable section

namespace NormLemmaProof

theorem eq_zero_of_powerSum_eq_zero {α : Type*} (s : Finset α) (a : α → ℂ)
    (h : ∀ j : ℕ, 1 ≤ j → ∑ i ∈ s, a i ^ j = 0) : ∀ i ∈ s, a i = 0 := by
  classical
  intro i₀ hi₀
  by_contra hb
  set b := a i₀ with hb_def
  set T := (s.image a).erase b
  set Q : Polynomial ℂ := Polynomial.X * ∏ c ∈ T, (Polynomial.X - Polynomial.C c) with hQ_def
  have hQ : ∀ x, Q.eval x = x * ∏ c ∈ T, (x - c) := by
    intro x; simp [Q, Polynomial.eval_prod]
  have h1 : ∑ i ∈ s, Q.eval (a i) = 0 := by
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Q]
    · rw [h k hk, mul_zero]
  have h2 : ∑ i ∈ s, Q.eval (a i) = ∑ i ∈ s, if a i = b then Q.eval b else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    split_ifs with hab
    · rw [hab]
    · rw [hQ]
      by_cases hai : a i = 0
      · simp [hai]
      · have hT : a i ∈ T := Finset.mem_erase.2 ⟨hab, Finset.mem_image_of_mem a hi⟩
        rw [Finset.prod_eq_zero hT (sub_self _), mul_zero]
  rw [h2, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at h1
  have hcard : ((s.filter fun i => a i = b).card : ℂ) ≠ 0 := by
    have hm : i₀ ∈ s.filter fun i => a i = b := Finset.mem_filter.2 ⟨hi₀, rfl⟩
    exact_mod_cast (Finset.card_pos.2 ⟨_, hm⟩).ne'
  have hQb : Q.eval b ≠ 0 := by
    rw [hQ]
    refine mul_ne_zero hb (Finset.prod_ne_zero_iff.2 fun c hc => sub_ne_zero.2 ?_)
    exact (Finset.ne_of_mem_erase hc).symm
  exact mul_ne_zero hcard hQb h1

theorem eq_zero_of_growth_of_order {g : ℂ → ℂ} {F : Set ℂ} (hF : F.Finite)
    (hd : ∀ t ∉ F, DifferentiableAt ℂ g t) {A B : ℝ} {d : ℕ}
    (hA : ∀ t ∉ F, ‖g t‖ ≤ A * (1 + ‖t‖) ^ d)
    (hB : ∀ᶠ t in 𝓝 (0 : ℂ), ‖g t‖ ≤ B * ‖t‖ ^ (d + 1)) :
    ∀ t ∉ F, g t = 0 := by
  set G : Set ℂ := insert 0 F with hG_def
  have hG : G.Finite := hF.insert 0
  set h : ℂ → ℂ := fun t => g t / t ^ (d + 1) with h_def
  have hdh : ∀ t ∉ G, DifferentiableAt ℂ h t := by
    intro t ht
    have ht0 : t ≠ 0 := fun e => ht (e ▸ Set.mem_insert 0 F)
    have htF : t ∉ F := fun e => ht (Set.mem_insert_of_mem 0 e)
    exact (hd t htF).div (differentiableAt_pow _) (pow_ne_zero _ ht0)
  set H : ℂ → ℂ := fun t => limUnder (𝓝[≠] t) h with H_def
  have hHh : ∀ t ∉ G, H t = h t := fun t ht =>
    ((hdh t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hloc : ∀ c : ℂ, ∃ r > 0, (∀ t ∈ ball c r, t ≠ c → t ∉ G) ∧
      BddAbove (norm ∘ h '' (ball c r \ {c})) := by
    intro c
    have hiso : (G \ {c})ᶜ ∈ 𝓝 c :=
      (hG.sdiff).isClosed.compl_mem_nhds (fun e => e.2 rfl)
    obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.mem_nhds_iff.1 hiso
    have hsep : ∀ t ∈ ball c r₁, t ≠ c → t ∉ G := fun t ht htc htG => hr₁s ht ⟨htG, htc⟩
    by_cases hc : c = 0
    · subst hc
      obtain ⟨r₂, hr₂, hr₂s⟩ := Metric.mem_nhds_iff.1 hB
      refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
        fun t ht htc => hsep t (ball_subset_ball (min_le_left _ _) ht) htc, ⟨B, ?_⟩⟩
      rintro _ ⟨t, ⟨ht, htc⟩, rfl⟩
      have ht0 : t ≠ 0 := htc
      have hpos : 0 < ‖t‖ ^ (d + 1) := pow_pos (norm_pos_iff.2 ht0) _
      have hle : ‖g t‖ ≤ B * ‖t‖ ^ (d + 1) := hr₂s (ball_subset_ball (min_le_right _ _) ht)
      simp only [Function.comp, h_def, norm_div, norm_pow]
      rw [div_le_iff₀ hpos]
      exact hle
    · have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
      refine ⟨min r₁ (‖c‖ / 2), lt_min hr₁ (by linarith),
        fun t ht htc => hsep t (ball_subset_ball (min_le_left _ _) ht) htc,
        ⟨|A| * (1 + 2 * ‖c‖) ^ d / (‖c‖ / 2) ^ (d + 1), ?_⟩⟩
      rintro _ ⟨t, ⟨ht, htc⟩, rfl⟩
      have htG := hsep t (ball_subset_ball (min_le_left _ _) ht) htc
      have htF : t ∉ F := fun e => htG (Set.mem_insert_of_mem 0 e)
      have hdist : ‖t - c‖ < ‖c‖ / 2 := by
        have h' := ball_subset_ball (min_le_right r₁ (‖c‖ / 2)) ht
        rwa [mem_ball, dist_eq_norm] at h'
      have hlow : ‖c‖ / 2 ≤ ‖t‖ := by
        have h' := norm_sub_norm_le c t
        rw [norm_sub_rev] at h'
        linarith
      have hup : ‖t‖ ≤ 2 * ‖c‖ := by
        have h' := norm_sub_norm_le t c
        linarith
      have hnum : ‖g t‖ ≤ |A| * (1 + 2 * ‖c‖) ^ d := by
        calc ‖g t‖ ≤ A * (1 + ‖t‖) ^ d := hA t htF
          _ ≤ |A| * (1 + ‖t‖) ^ d :=
              mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
          _ ≤ |A| * (1 + 2 * ‖c‖) ^ d := by gcongr
      simp only [Function.comp, h_def, norm_div, norm_pow]
      exact div_le_div₀ (by positivity) hnum (by positivity)
        (pow_le_pow_left₀ (by positivity) hlow _)
  have hHd : Differentiable ℂ H := by
    intro c
    obtain ⟨r, hr, hsep, hbdd⟩ := hloc c
    have hdiffOn : DifferentiableOn ℂ h (ball c r \ {c}) := fun t ht =>
      (hdh t (hsep t ht.1 ht.2)).differentiableWithinAt
    have hupd := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hr)
      hdiffOn hbdd
    have heq : H =ᶠ[𝓝 c] Function.update h c (limUnder (𝓝[≠] c) h) := by
      filter_upwards [ball_mem_nhds c hr] with t ht
      by_cases htc : t = c
      · subst htc; simp [H_def]
      · rw [Function.update_of_ne htc, hHh t (hsep t ht htc)]
    exact (hupd.differentiableAt (ball_mem_nhds c hr)).congr_of_eventuallyEq heq
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hG.isBounded
  have hfar : ∀ t : ℂ, max R 1 < ‖t‖ → ‖H t‖ ≤ |A| * 2 ^ d / ‖t‖ := by
    intro t ht
    have htG : t ∉ G := fun e => by
      have h' := hR e
      rw [mem_closedBall, dist_zero_right] at h'
      linarith [le_max_left R 1]
    have htF : t ∉ F := fun e => htG (Set.mem_insert_of_mem 0 e)
    have h1 : 1 < ‖t‖ := lt_of_le_of_lt (le_max_right R 1) ht
    have htpos : 0 < ‖t‖ := by linarith
    rw [hHh t htG]
    simp only [h_def, norm_div, norm_pow]
    rw [div_le_div_iff₀ (pow_pos htpos _) htpos]
    calc ‖g t‖ * ‖t‖ ≤ (|A| * (2 * ‖t‖) ^ d) * ‖t‖ := by
          gcongr
          calc ‖g t‖ ≤ A * (1 + ‖t‖) ^ d := hA t htF
            _ ≤ |A| * (1 + ‖t‖) ^ d :=
                mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
            _ ≤ |A| * (2 * ‖t‖) ^ d := by gcongr; linarith
      _ = |A| * 2 ^ d * ‖t‖ ^ (d + 1) := by ring
  have hbound : Bornology.IsBounded (Set.range H) := by
    have hK := (isCompact_closedBall (0 : ℂ) (max R 1)).image hHd.continuous
    refine (hK.isBounded.union (isBounded_closedBall (x := (0 : ℂ)) (r := |A| * 2 ^ d))).subset ?_
    rintro _ ⟨t, rfl⟩
    by_cases ht : ‖t‖ ≤ max R 1
    · exact Or.inl ⟨t, by simpa using ht, rfl⟩
    · push Not at ht
      refine Or.inr ?_
      rw [mem_closedBall, dist_zero_right]
      have h1 : 1 ≤ ‖t‖ := le_trans (le_max_right R 1) ht.le
      calc ‖H t‖ ≤ |A| * 2 ^ d / ‖t‖ := hfar t ht
        _ ≤ |A| * 2 ^ d / 1 := by gcongr
        _ = _ := div_one _
  have hconst : ∀ t, H t = H 0 := fun t => hHd.apply_eq_apply_of_bounded hbound t 0
  have hH0 : H 0 = 0 := by
    have hle : ∀ N : ℕ, max R 1 < N → ‖H 0‖ ≤ |A| * 2 ^ d / N := by
      intro N hN
      rw [← hconst N]
      have h' := hfar (N : ℂ) (by rw [Complex.norm_natCast]; exact hN)
      rwa [Complex.norm_natCast] at h'
    have htend := tendsto_const_div_atTop_nhds_zero_nat (|A| * 2 ^ d)
    have hev : ∀ᶠ N : ℕ in atTop, ‖H 0‖ ≤ |A| * 2 ^ d / N := by
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max R 1)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact hle N (lt_of_lt_of_le hN₀ (by exact_mod_cast hN))
    exact norm_le_zero_iff.1 (ge_of_tendsto htend hev)
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    have h' := hB.self_of_nhds
    simp only [norm_zero, zero_pow (Nat.succ_ne_zero d), mul_zero] at h'
    exact norm_le_zero_iff.1 h'
  have htG : t ∉ G := by
    rintro (e | e)
    · exact ht0 e
    · exact ht e
  have h' := hHh t htG
  rw [hconst t, hH0] at h'
  have hp : t ^ (d + 1) ≠ 0 := pow_ne_zero _ ht0
  have h'' : g t / t ^ (d + 1) = 0 := h'.symm
  exact (div_eq_zero_iff.1 h'').resolve_right hp

theorem normSq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem normSq_smul {n : ℕ} (t : ℂ) (v : Fin n → ℂ) : normSq (t • v) = ‖t‖ ^ 2 * normSq v := by
  simp only [normSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem rpow_half_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b ^ 2) (m : ℕ) :
    a ^ ((m : ℝ) / 2) ≤ b ^ m := by
  calc a ^ ((m : ℝ) / 2) ≤ (b ^ 2) ^ ((m : ℝ) / 2) := Real.rpow_le_rpow ha hab (by positivity)
    _ = b ^ m := by
      rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb,
        show ((2 : ℕ) : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem finite_zeros_on_line {n : ℕ} (De : MvPolynomial (Fin n) ℂ)
    (h0 : MvPolynomial.eval 0 De ≠ 0) (v : Fin n → ℂ) :
    {t : ℂ | MvPolynomial.eval (t • v) De = 0}.Finite := by
  have hP : ∀ (p : MvPolynomial (Fin n) ℂ) (t : ℂ),
      (MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) p).eval t =
        MvPolynomial.eval (t • v) p := by
    intro p t
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp =>
      rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, map_mul, MvPolynomial.eval_X, Pi.smul_apply, smul_eq_mul]
      ring
  set P : Polynomial ℂ := MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) De
  have hP0 : P ≠ 0 := by
    intro h
    apply h0
    have h1 := hP De 0
    rw [zero_smul] at h1
    rw [← h1]
    show Polynomial.eval 0 P = 0
    rw [h, Polynomial.eval_zero]
  refine (Polynomial.finite_setOfPred_isRoot hP0).subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, P, hP]
  exact ht

section Sheets

variable {MS : Type} [TopologicalSpace MS] {X : Type} [TopologicalSpace X]

theorem exists_sheets {z : MS → X} {B : Set X} (hB : IsOpen B) (hz : ∀ p, z p ∈ B)
    (hcov : IsCoveringMap (B.codRestrict z hz)) {x₀ : X} (hx₀ : x₀ ∈ B)
    (hfin : (z ⁻¹' {x₀}).Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (σ : ι → X → MS) (W : Set X), IsOpen W ∧ x₀ ∈ W ∧
      (∀ i, ContinuousOn (σ i) W) ∧ (∀ y ∈ W, ∀ i, z (σ i y) = y) ∧
      (∀ y ∈ W, Set.BijOn (fun i => σ i y) Set.univ (z ⁻¹' {y})) := by
  classical
  set f := B.codRestrict z hz with hf
  obtain ⟨_, U, hxU, hUo, hfU, H, hH⟩ := hcov ⟨x₀, hx₀⟩
  have hfib : (f ⁻¹' {⟨x₀, hx₀⟩} : Set MS) = z ⁻¹' {x₀} := by
    ext q; simp [f, Subtype.ext_iff]
  have : Finite (f ⁻¹' {⟨x₀, hx₀⟩}) := by rw [hfib]; exact hfin.to_subtype
  let τ : (f ⁻¹' {⟨x₀, hx₀⟩}) → B → MS := fun i b =>
    if hb : b ∈ U then ((H.symm (⟨b, hb⟩, i)) : MS) else (i : MS)
  let σ : (f ⁻¹' {⟨x₀, hx₀⟩}) → X → MS := fun i y =>
    if hy : y ∈ B then τ i ⟨y, hy⟩ else (i : MS)
  have hσ : ∀ i (b : B) (hb : b ∈ U), σ i b = ((H.symm (⟨b, hb⟩, i)) : MS) := by
    intro i b hb
    simp only [σ, τ, dif_pos b.2, Subtype.coe_eta, dif_pos hb]
  have hzH : ∀ (b : B) (hb : b ∈ U) i, z ((H.symm (⟨b, hb⟩, i)) : MS) = b := by
    intro b hb i
    have h1 := hH (H.symm (⟨b, hb⟩, i))
    rw [H.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val h1
    simpa [f] using h2.symm
  refine ⟨f ⁻¹' {⟨x₀, hx₀⟩}, Fintype.ofFinite _, σ, Subtype.val '' U,
    hB.isOpenMap_subtype_val U hUo, ⟨⟨x₀, hx₀⟩, hxU, rfl⟩, ?_, ?_, ?_⟩
  · intro i
    rintro _ ⟨b, hb, rfl⟩
    have hτ : ContinuousOn (τ i) U := by
      rw [continuousOn_iff_continuous_domRestrict]
      have he : U.domRestrict (τ i) = fun b : U => ((H.symm (b, i)) : MS) := by
        funext b
        simp only [Set.domRestrict_apply, τ, dif_pos b.2]
      rw [he]
      exact continuous_subtype_val.comp
        (H.symm.continuous.comp (Continuous.prodMk continuous_id continuous_const))
    have hτb : ContinuousAt (τ i) b := hτ.continuousAt (hUo.mem_nhds hb)
    have hres : B.domRestrict (σ i) = τ i := by
      funext b'
      simp only [Set.domRestrict_apply, σ, dif_pos b'.2, Subtype.coe_eta]
    have hw : ContinuousWithinAt (σ i) B b := by
      rw [continuousWithinAt_iff_continuousAt_domRestrict _ b.2, hres]
      exact hτb
    exact (hw.continuousAt (hB.mem_nhds b.2)).continuousWithinAt
  · rintro _ ⟨b, hb, rfl⟩ i
    rw [hσ i b hb]
    exact hzH b hb i
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨fun i _ => ?_, fun i _ j _ hij => ?_, fun q hq => ?_⟩
    · show z (σ i b) = b
      rw [hσ i b hb]
      exact hzH b hb i
    · simp only [hσ _ b hb] at hij
      have h1 := H.symm.injective (Subtype.ext hij)
      exact congrArg Prod.snd h1
    · have hfq : f q = b := Subtype.ext (by simpa [f] using hq)
      have hqU : q ∈ f ⁻¹' U := by
        show f q ∈ U
        rw [hfq]; exact hb
      refine ⟨(H ⟨q, hqU⟩).2, trivial, ?_⟩
      show σ _ b = q
      rw [hσ _ b hb]
      have h1 : (H ⟨q, hqU⟩).1 = ⟨b, hb⟩ := by
        apply Subtype.ext
        rw [hH]
        exact hfq
      have h2 : H.symm (⟨b, hb⟩, (H ⟨q, hqU⟩).2) = ⟨q, hqU⟩ := by
        rw [H.symm_apply_eq]
        exact Prod.ext h1.symm rfl
      rw [h2]

end Sheets

section Lines

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

theorem differentiableAt_comp_section {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) {σ : (Fin n → ℂ) → MS} {x₀ : Fin n → ℂ}
    (hc : ContinuousAt σ x₀) (hz : ∀ᶠ y in 𝓝 x₀, z (σ y) = y) :
    DifferentiableAt ℂ (u ∘ σ) x₀ := by
  obtain ⟨e, hp, hze, han⟩ := hu (σ x₀)
  have hx₀ : z (σ x₀) = x₀ := hz.self_of_nhds
  have ht : x₀ ∈ e.target := by
    have h1 := e.map_source hp
    rwa [← hze _ hp, hx₀] at h1
  have hsrc : ∀ᶠ y in 𝓝 x₀, σ y ∈ e.source := hc.preimage_mem_nhds (e.open_source.mem_nhds hp)
  have heq : u ∘ σ =ᶠ[𝓝 x₀] u ∘ e.symm := by
    filter_upwards [hsrc, hz] with y h1 h2
    show u (σ y) = u (e.symm y)
    congr 1
    calc σ y = e.symm (e (σ y)) := (e.left_inv h1).symm
      _ = e.symm y := by rw [← hze _ h1, h2]
  exact (han x₀ ht).differentiableAt.congr_of_eventuallyEq heq

theorem powerSum_differentiableAt {z : MS → (Fin n → ℂ)} {B : Set (Fin n → ℂ)} {δ : ℕ}
    {u : MS → ℂ} (hB : IsOpen B) (hcov : IsCoveringOfDegree z B δ) (hu : HolomorphicAlong z u)
    (v : Fin n → ℂ) (j : ℕ) {t₀ : ℂ} (ht₀ : t₀ • v ∈ B) :
    DifferentiableAt ℂ (fun t : ℂ => ∑ᶠ q ∈ z ⁻¹' {t • v}, u q ^ j) t₀ := by
  obtain ⟨hz, hc, hdeg⟩ := hcov
  obtain ⟨ι, _, σ, W, hWo, hxW, hσc, hσz, hσb⟩ :=
    exists_sheets hB hz hc ht₀ (Set.finite_of_encard_eq_coe (hdeg _ ht₀))
  have hline : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 t₀, t • v ∈ W := hline.continuousAt.preimage_mem_nhds (hWo.mem_nhds hxW)
  have heq : (fun t : ℂ => ∑ᶠ q ∈ z ⁻¹' {t • v}, u q ^ j) =ᶠ[𝓝 t₀]
      fun t => ∑ i, u (σ i (t • v)) ^ j := by
    filter_upwards [hev] with t ht
    have h1 := finsum_mem_eq_of_bijOn (f := fun i => u (σ i (t • v)) ^ j)
      (g := fun q => u q ^ j) (fun i => σ i (t • v)) (hσb _ ht) (fun i _ => rfl)
    rw [← h1, finsum_mem_univ, finsum_eq_sum_of_fintype]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.fun_sum fun i _ => ?_
  have hs : DifferentiableAt ℂ (u ∘ σ i) (t₀ • v) :=
    differentiableAt_comp_section hu ((hσc i).continuousAt (hWo.mem_nhds hxW))
      (Filter.mem_of_superset (hWo.mem_nhds hxW) fun y hy => hσz y hy i)
  have hl : DifferentiableAt ℂ (fun t : ℂ => t • v) t₀ := differentiableAt_id.smul_const v
  exact (hs.comp t₀ hl).pow j

theorem powerSum_growth {z : MS → (Fin n → ℂ)} {B : Set (Fin n → ℂ)} {δ : ℕ} {u : MS → ℂ}
    {C : ℝ} {m : ℕ} (hcov : IsCoveringOfDegree z B δ)
    (hgrowth : ∀ p, ‖u p‖ ≤ C * (1 + normSq (z p)) ^ ((m : ℝ) / 2)) (v : Fin n → ℂ) (j : ℕ)
    (t : ℂ) (ht : t • v ∈ B) :
    ‖∑ᶠ q ∈ z ⁻¹' {t • v}, u q ^ j‖ ≤
      (δ * max C 0 ^ j * (1 + Real.sqrt (normSq v)) ^ (m * j)) * (1 + ‖t‖) ^ (m * j) := by
  obtain ⟨-, -, hdeg⟩ := hcov
  have hfin : (z ⁻¹' {t • v}).Finite := Set.finite_of_encard_eq_coe (hdeg _ ht)
  have hcard : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hdeg _ ht] at h1
    exact_mod_cast h1.symm
  set s := Real.sqrt (normSq v) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hK : normSq v = s ^ 2 := (Real.sq_sqrt (normSq_nonneg v)).symm
  set b := (1 + s) * (1 + ‖t‖) with hb
  have hb0 : 0 ≤ b := by positivity
  have hterm : ∀ q ∈ hfin.toFinset, ‖u q ^ j‖ ≤ max C 0 ^ j * b ^ (m * j) := by
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    have hzq : z q = t • v := hq
    rw [norm_pow, pow_mul, ← mul_pow]
    gcongr
    calc ‖u q‖ ≤ C * (1 + normSq (z q)) ^ ((m : ℝ) / 2) := hgrowth q
      _ ≤ max C 0 * (1 + normSq (z q)) ^ ((m : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (by linarith [normSq_nonneg (z q)]) _)
      _ ≤ max C 0 * b ^ m := by
          gcongr
          apply rpow_half_le (by linarith [normSq_nonneg (z q)]) hb0
          rw [hzq, normSq_smul, hK, hb]
          have hτ := norm_nonneg t
          nlinarith [mul_nonneg hs0 hτ, mul_nonneg (mul_nonneg hs0 hτ) hs0,
            mul_nonneg (mul_nonneg hs0 hτ) hτ, sq_nonneg (s + ‖t‖), sq_nonneg (s * ‖t‖)]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ‖∑ q ∈ hfin.toFinset, u q ^ j‖ ≤ ∑ q ∈ hfin.toFinset, ‖u q ^ j‖ := norm_sum_le _ _
    _ ≤ hfin.toFinset.card • (max C 0 ^ j * b ^ (m * j)) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = _ := by rw [hcard, nsmul_eq_mul, hb, mul_pow]; ring

theorem powerSum_order {z : MS → (Fin n → ℂ)} {B : Set (Fin n → ℂ)} {δ : ℕ} {u : MS → ℂ}
    {m : ℕ} (hB : IsOpen B) (hcov : IsCoveringOfDegree z B δ)
    (horder : ∀ p, z p = 0 → OrderGT z u p m) (h0B : (0 : Fin n → ℂ) ∈ B) (v : Fin n → ℂ)
    {j : ℕ} (hj : 1 ≤ j) :
    ∃ K : ℝ, ∀ᶠ t in 𝓝 (0 : ℂ), ‖∑ᶠ q ∈ z ⁻¹' {t • v}, u q ^ j‖ ≤ K * ‖t‖ ^ (m * j + 1) := by
  obtain ⟨hz, hc, hdeg⟩ := hcov
  obtain ⟨ι, _, σ, W, hWo, hxW, hσc, hσz, hσb⟩ :=
    exists_sheets hB hz hc h0B (Set.finite_of_encard_eq_coe (hdeg _ h0B))
  choose Ci hCi using fun i => horder (σ i 0) (hσz 0 hxW i)
  set s := Real.sqrt (normSq v) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  refine ⟨∑ i, (max (Ci i) 0 * s ^ (m + 1)) ^ j, ?_⟩
  have hL : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 0) := by
    have hline : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
    have h1 := hline.tendsto 0
    rwa [zero_smul] at h1
  have hW' : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ W := hL.eventually (hWo.mem_nhds hxW)
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℂ), ‖t‖ ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with t ht
    simpa using ht
  have hsh : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i, ‖u (σ i (t • v))‖ ≤
      Ci i * Real.sqrt (normSq (z (σ i (t • v)) - z (σ i 0))) ^ (m + 1) := by
    refine Filter.eventually_all.2 fun i => ?_
    have hσ0 : ContinuousAt (σ i) 0 := (hσc i).continuousAt (hWo.mem_nhds hxW)
    exact (hσ0.tendsto.comp hL).eventually (hCi i)
  filter_upwards [hW', hsmall, hsh] with t ht ht1 htb
  have h1 := finsum_mem_eq_of_bijOn (f := fun i => u (σ i (t • v)) ^ j)
    (g := fun q => u q ^ j) (fun i => σ i (t • v)) (hσb _ ht) (fun i _ => rfl)
  rw [← h1, finsum_mem_univ, finsum_eq_sum_of_fintype]
  have hτ := norm_nonneg t
  have hpow : ‖t‖ ^ ((m + 1) * j) ≤ ‖t‖ ^ (m * j + 1) :=
    pow_le_pow_of_le_one hτ ht1 (by rw [add_mul, one_mul]; omega)
  calc ‖∑ i, u (σ i (t • v)) ^ j‖ ≤ ∑ i, ‖u (σ i (t • v)) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ i, (max (Ci i) 0 * s ^ (m + 1)) ^ j * ‖t‖ ^ ((m + 1) * j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow, pow_mul, ← mul_pow]
        gcongr
        have hzi : z (σ i (t • v)) = t • v := hσz _ ht i
        have hz0 : z (σ i 0) = 0 := hσz 0 hxW i
        have hsq : Real.sqrt (normSq (z (σ i (t • v)) - z (σ i 0))) = ‖t‖ * s := by
          rw [hzi, hz0, sub_zero, normSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hτ]
        calc ‖u (σ i (t • v))‖ ≤ Ci i * Real.sqrt (normSq (z (σ i (t • v)) - z (σ i 0))) ^ (m + 1) :=
              htb i
          _ ≤ max (Ci i) 0 * (‖t‖ * s) ^ (m + 1) := by
              rw [hsq]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ = max (Ci i) 0 * s ^ (m + 1) * ‖t‖ ^ (m + 1) := by ring
    _ ≤ ∑ i, (max (Ci i) 0 * s ^ (m + 1)) ^ j * ‖t‖ ^ (m * j + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (∑ i, (max (Ci i) 0 * s ^ (m + 1)) ^ j) * ‖t‖ ^ (m * j + 1) := by
        rw [Finset.sum_mul]

end Lines

end NormLemmaProof

open NormLemmaProof in

theorem NormLemma.proof : NormLemma.Statement := by
  intro n MS _ _ _ _ De z δ u C m hDe hcov hu hgrowth horder
  have hBo : IsOpen (complementOf De) :=
    isOpen_ne_fun (MvPolynomial.continuous_eval De) continuous_const
  have h0B : (0 : Fin n → ℂ) ∈ complementOf De := hDe
  funext p
  set v := z p with hv
  have hvB : v ∈ complementOf De := hcov.1 p
  set F : Set ℂ := {t | t • v ∉ complementOf De} with hF_def
  have hF : F.Finite := (finite_zeros_on_line De hDe v).subset fun t ht => by
    simpa [hF_def, complementOf] using ht
  have hps : ∀ j, 1 ≤ j → ∑ᶠ q ∈ z ⁻¹' {v}, u q ^ j = 0 := by
    intro j hj
    obtain ⟨K, hK⟩ := powerSum_order hBo hcov horder h0B v hj
    have h1 := eq_zero_of_growth_of_order (g := fun t : ℂ => ∑ᶠ q ∈ z ⁻¹' {t • v}, u q ^ j) hF
      (fun t ht => powerSum_differentiableAt hBo hcov hu v j (by simpa [hF_def] using ht))
      (fun t ht => powerSum_growth hcov hgrowth v j t (by simpa [hF_def] using ht)) hK
    simpa using h1 1 (by simpa [hF_def] using hvB)
  obtain ⟨-, -, hdeg⟩ := hcov
  have hfinv : (z ⁻¹' {v}).Finite := Set.finite_of_encard_eq_coe (hdeg v hvB)
  have h2 := eq_zero_of_powerSum_eq_zero hfinv.toFinset u fun j hj => by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfinv]
    exact hps j hj
  exact h2 p (by simp [hv])

end

end GroundTheory.Heights₂.Heights.EffectiveHS
