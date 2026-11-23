import Mathlib

open MeasureTheory Filter Topology Set

namespace GlobalTheory.CompanionTheory.EisRk1Cont

lemma continuous_setIntegral_Ioi_one {Z : Type*} [TopologicalSpace Z] (F : Z → ℝ → ℂ)
    (hF : ∀ z y, 1 ≤ y → ContinuousAt (fun w : Z × ℝ ↦ F w.1 w.2) (z, y))
    (hb : ∀ z₀, ∃ V ∈ 𝓝 z₀, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ V, ∀ x : ℝ, 1 ≤ x → ‖F z x‖ ≤ M * x ^ (-3 : ℝ)) :
    Continuous fun z ↦ ∫ x in Ioi (1 : ℝ), F z x := by
  have e2 : ∀ x : ℝ, 0 < x → x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx.le]; congr 1; exact_mod_cast Real.rpow_natCast x 2
  have e3 : ∀ x : ℝ, 0 < x → x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx.le]; congr 1; exact_mod_cast Real.rpow_natCast x 3
  have hcont : ∀ z, ContinuousOn (F z) (Ioi 1) := fun z y hy =>
    (ContinuousAt.comp_of_eq (hF z y (le_of_lt hy))
      (by fun_prop : Continuous fun t : ℝ => (z, t)).continuousAt rfl).continuousWithinAt
  have hint : ∀ z, IntegrableOn (F z) (Ioi 1) := by
    intro z
    obtain ⟨V, hV, M, -, hM⟩ := hb z
    refine Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).const_mul M)
      ((hcont z).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    exact hM z (mem_of_mem_nhds hV) x (le_of_lt hx)
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨V, hV, M, hM0, hM⟩ := hb z₀
  obtain ⟨R, hR1, hRM⟩ : ∃ R : ℝ, 1 ≤ R ∧ 4 * M / ε ≤ R :=
    ⟨max 1 (4 * M / ε), le_max_left _ _, le_max_right _ _⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hδ0 : 0 < ε / 2 * (R ^ 2)⁻¹ := mul_pos (half_pos hε) (inv_pos.mpr (pow_pos hR0 2))
  have hunif : ∀ᶠ z in 𝓝 z₀, ∀ y ∈ Icc (1 : ℝ) R,
      dist (F z y) (F z₀ y) < ε / 2 * (R ^ 2)⁻¹ := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun y hy => ?_
    have h1 := Metric.tendsto_nhds.mp (hF z₀ y hy.1).tendsto _ (half_pos hδ0)
    have h2 := Metric.tendsto_nhds.mp
      (ContinuousAt.comp_of_eq (hF z₀ y hy.1)
        ((by fun_prop : Continuous fun p : Z × ℝ => (z₀, p.2)).continuousAt (x := (z₀, y))) rfl).tendsto
      _ (half_pos hδ0)
    filter_upwards [h1, h2] with p hp1 hp2
    calc dist (F p.1 p.2) (F z₀ p.2)
        ≤ dist (F p.1 p.2) (F z₀ y) + dist (F z₀ p.2) (F z₀ y) := dist_triangle_right _ _ _
      _ < ε / 2 * (R ^ 2)⁻¹ / 2 + ε / 2 * (R ^ 2)⁻¹ / 2 := add_lt_add hp1 hp2
      _ = ε / 2 * (R ^ 2)⁻¹ := add_halves _
  have hg : IntegrableOn (fun x : ℝ => ε / 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul _
  have hgi : ∫ x in Ioi (1 : ℝ), ε / 2 * x ^ (-2 : ℝ) = ε / 2 := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
    norm_num
  filter_upwards [hV, hunif] with z hzV hz
  have key : ‖∫ x in Ioi (1 : ℝ), F z x - F z₀ x‖ ≤ ∫ x in Ioi (1 : ℝ), ε / 2 * x ^ (-2 : ℝ) := by
    refine norm_integral_le_of_norm_le hg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx1
    show ‖F z x - F z₀ x‖ ≤ ε / 2 * x ^ (-2 : ℝ)
    rw [e2 x hx0]
    rcases le_or_gt x R with hxR | hxR
    · rw [← dist_eq_norm]
      refine le_trans (hz x ⟨le_of_lt hx1, hxR⟩).le ?_
      have hsq : x ^ 2 ≤ R ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hx0 2) hsq) (half_pos hε).le
    · have h4 : 4 * M < ε * x := by
        have h' : 4 * M / ε < x := lt_of_le_of_lt hRM hxR
        rw [div_lt_iff₀ hε] at h'
        linarith
      calc ‖F z x - F z₀ x‖ ≤ ‖F z x‖ + ‖F z₀ x‖ := norm_sub_le _ _
        _ ≤ M * x ^ (-3 : ℝ) + M * x ^ (-3 : ℝ) :=
            add_le_add (hM z hzV x hx1.le) (hM z₀ (mem_of_mem_nhds hV) x hx1.le)
        _ = 2 * M * x⁻¹ * (x ^ 2)⁻¹ := by rw [e3 x hx0]; ring
        _ ≤ ε / 2 * (x ^ 2)⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (pow_nonneg hx0.le 2))
            rw [← div_eq_mul_inv, div_le_iff₀ hx0]
            linarith
  rw [hgi] at key
  rw [dist_eq_norm, ← integral_sub (hint z) (hint z₀)]
  linarith

lemma continuous_mellinTail {X : Type*} [TopologicalSpace X] (φ : X → ℝ → ℂ)
    (hφ : ContinuousOn (fun q : X × ℝ ↦ φ q.1 q.2) (univ ×ˢ Ioi 0))
    (hb : ∀ p₀ : X, ∀ r : ℝ, ∃ U ∈ 𝓝 p₀, ∃ M : ℝ, ∀ p ∈ U, ∀ x : ℝ, 1 ≤ x →
      ‖φ p x‖ ≤ M * x ^ (-r)) :
    Continuous fun q : ℂ × X ↦ ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (q.1 - 1) * φ q.2 x := by
  refine GlobalTheory.CompanionTheory.EisRk1Cont.continuous_setIntegral_Ioi_one
    (fun (q : ℂ × X) (x : ℝ) => (x : ℂ) ^ (q.1 - 1) * φ q.2 x) ?_ ?_
  · intro q y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
    have h1 : ContinuousAt (fun w : (ℂ × X) × ℝ => ((w.2 : ℝ) : ℂ) ^ (w.1.1 - 1)) (q, y) :=
      ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_snd).continuousAt
        ((continuous_fst.comp continuous_fst).sub continuous_const).continuousAt
        (Complex.ofReal_mem_slitPlane.mpr hy0)
    have h2 : ContinuousAt (fun w : (ℂ × X) × ℝ => φ w.1.2 w.2) (q, y) :=
      ContinuousAt.comp_of_eq
        (hφ.continuousAt (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds hy0)))
        (by fun_prop : Continuous fun w : (ℂ × X) × ℝ => (w.1.2, w.2)).continuousAt rfl
    exact h1.mul h2
  · rintro ⟨s₀, p₀⟩
    obtain ⟨U, hU, M, hM⟩ := hb p₀ (s₀.re + 3)
    refine ⟨{s : ℂ | s.re < s₀.re + 1} ×ˢ U,
      prod_mem_nhds ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show s₀.re < s₀.re + 1 by linarith)) hU, max M 0, le_max_right _ _, ?_⟩
    rintro ⟨s, p⟩ ⟨hs, hp⟩ x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hs1 : s.re < s₀.re + 1 := hs
    have hs' : (s - 1).re ≤ s₀.re := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    calc ‖(x : ℂ) ^ (s - 1) * φ p x‖ = x ^ (s - 1).re * ‖φ p x‖ := by
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      _ ≤ x ^ s₀.re * (max M 0 * x ^ (-(s₀.re + 3))) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx hs')
            ((hM p hp x hx).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)))
            (norm_nonneg _) (Real.rpow_nonneg hx0.le _)
      _ = max M 0 * x ^ (-3 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add hx0]; congr 2; ring

lemma Λ₀_eq_tails (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) +
      P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀ :=
    ⟨_, rfl⟩
  have htop : P.f_modif =O[atTop] fun x : ℝ => x ^ (-(s.re + 1)) := by
    simpa using P.hf_modif_top (-(s.re + 1))
  have hbot : P.f_modif =O[𝓝[>] 0] fun x : ℝ => x ^ (-(s.re - 1)) := by
    refine (P.hf_zero (-(s.re - 1))).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
    have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_irrefl _ (ht.2.trans h)
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_notMem ht',
      Set.indicator_of_mem ht, zero_add]
  have hconv : MellinConvergent P.f_modif s :=
    mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) P.hf_modif_int htop
      (by linarith) hbot (by linarith)
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t) (Ioi 0) := hconv
  have hsplit : P.Λ₀ s = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t) +
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t := by
    rw [WeakFEPair.Λ₀, mellin, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self)
      (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hA : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (P.f x - P.f₀) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : t ∉ Ioo (0 : ℝ) 1 := fun h => lt_irrefl _ (h.2.trans ht)
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem ht,
      Set.indicator_of_notMem ht', add_zero, smul_eq_mul]
  have hfm : ∀ t ∈ Ioo (0 : ℝ) 1, P.f_modif t = G t := fun t ht => by
    have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_irrefl _ (ht.2.trans h)
    rw [hG]
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_notMem ht',
      Set.indicator_of_mem ht, zero_add]
  have hB : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t =
      P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) := by
    calc ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t
        = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t := integral_Ioc_eq_integral_Ioo
      _ = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G t :=
          setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [hfm t ht]
      _ = ∫ t in Ioi (0 : ℝ) ∩ Ioo 0 1, (t : ℂ) ^ (s - 1) • G t := by
          rw [Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
      _ = ∫ t in Ioi (0 : ℝ), Set.indicator (Ioo 0 1) (fun t : ℝ => (t : ℂ) ^ (s - 1) • G t) t :=
          (setIntegral_indicator measurableSet_Ioo).symm
      _ = mellin (Set.indicator (Ioo 0 1) G) s := by
          rw [mellin]; congr 1; funext t
          by_cases ht : t ∈ Ioo (0 : ℝ) 1
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
      _ = mellin (fun u : ℝ => Set.indicator (Ioo 0 1) G u⁻¹) (-s) := by
          rw [← mellin_comp_inv]; simp only [inv_inv]
      _ = ∫ u in Ioi (0 : ℝ), Set.indicator (Ioi 1)
            (fun x : ℝ => P.ε * ((x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀))) u := by
          rw [mellin]
          refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
          have hu0 : (0 : ℝ) < u := hu
          rcases le_or_gt u 1 with hu1 | hu1
          · have h1 : u⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h =>
              (not_lt.mpr ((one_le_inv₀ hu0).mpr hu1)) h.2
            have h2 : u ∉ Ioi (1 : ℝ) := fun h => (not_lt.mpr hu1) h
            rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, smul_zero]
          · have h1 : u⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr hu0, inv_lt_one_of_one_lt₀ hu1⟩
            have h2 : u ∈ Ioi (1 : ℝ) := hu1
            have hfe : P.f u⁻¹ = (P.ε * ((u ^ P.k : ℝ) : ℂ)) • P.g u := by
              rw [← one_div]; exact P.h_feq u hu0
            have hpow : u⁻¹ ^ (-P.k) = u ^ P.k := by
              rw [Real.inv_rpow hu0.le, Real.rpow_neg hu0.le, inv_inv]
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, hG]
            simp only [hfe, hpow, smul_eq_mul]
            rw [Complex.ofReal_cpow hu0.le, show (P.k : ℂ) - s - 1 = (P.k : ℂ) + (-s - 1) by ring,
              Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne')]
            ring
      _ = ∫ u in Ioi (0 : ℝ) ∩ Ioi 1, P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g u - P.g₀)) :=
          setIntegral_indicator measurableSet_Ioi
      _ = ∫ u in Ioi (1 : ℝ), P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g u - P.g₀)) := by
          rw [Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
      _ = P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) :=
          integral_const_mul _ _
  rw [hsplit, hA, hB]
  exact add_comm _ _

theorem weakFEPair_continuous_Λ₀ {X : Type*} [TopologicalSpace X] (P : X → WeakFEPair ℂ) (k : ℝ)
    (hk : ∀ p, (P p).k = k) (ε : ℂ) (hε : ∀ p, (P p).ε = ε)
    (hf : ContinuousOn (fun q : X × ℝ ↦ (P q.1).f q.2) (Set.univ ×ˢ Set.Ioi 0))
    (hg : ContinuousOn (fun q : X × ℝ ↦ (P q.1).g q.2) (Set.univ ×ˢ Set.Ioi 0))
    (hf₀ : Continuous fun p ↦ (P p).f₀) (hg₀ : Continuous fun p ↦ (P p).g₀)
    (hbd : ∀ p₀ : X, ∀ r : ℝ, ∃ U ∈ 𝓝 p₀, ∃ M : ℝ, ∀ p ∈ U, ∀ x : ℝ, 1 ≤ x →
      ‖(P p).f x - (P p).f₀‖ ≤ M * x ^ (-r) ∧ ‖(P p).g x - (P p).g₀‖ ≤ M * x ^ (-r)) :
    Continuous fun q : ℂ × X ↦ (P q.2).Λ₀ q.1 := by
  have h1 : Continuous fun q : ℂ × X ↦
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (q.1 - 1) * ((P q.2).f x - (P q.2).f₀) :=
    GlobalTheory.CompanionTheory.EisRk1Cont.continuous_mellinTail (fun p x ↦ (P p).f x - (P p).f₀)
      (hf.sub (hf₀.comp continuous_fst).continuousOn)
      (fun p₀ r ↦ by
        obtain ⟨U, hU, M, hM⟩ := hbd p₀ r
        exact ⟨U, hU, M, fun p hp x hx ↦ (hM p hp x hx).1⟩)
  have h2 : Continuous fun q : ℂ × X ↦
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (q.1 - 1) * ((P q.2).g x - (P q.2).g₀) :=
    GlobalTheory.CompanionTheory.EisRk1Cont.continuous_mellinTail (fun p x ↦ (P p).g x - (P p).g₀)
      (hg.sub (hg₀.comp continuous_fst).continuousOn)
      (fun p₀ r ↦ by
        obtain ⟨U, hU, M, hM⟩ := hbd p₀ r
        exact ⟨U, hU, M, fun p hp x hx ↦ (hM p hp x hx).2⟩)
  have h3 : Continuous fun q : ℂ × X ↦ ((k : ℂ) - q.1, q.2) := by fun_prop
  have h4 := h2.comp h3
  have heq : (fun q : ℂ × X ↦ (P q.2).Λ₀ q.1) = fun q ↦
      (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (q.1 - 1) * ((P q.2).f x - (P q.2).f₀)) +
        ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (((k : ℂ) - q.1) - 1) * ((P q.2).g x - (P q.2).g₀) := by
    funext q
    rw [GlobalTheory.CompanionTheory.EisRk1Cont.Λ₀_eq_tails, hk, hε]
  rw [heq]
  exact h1.add (continuous_const.mul h4)

end GlobalTheory.CompanionTheory.EisRk1Cont
