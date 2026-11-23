import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslationSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSmallTranslationContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantOperatorTranslateStatement
open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

theorem rapidDecay_omega_of_invariant {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] (P : V → V → ℝ)
    (hP : IsPairing P) (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V₁ ℂ) {ι : Type} [Fintype ι]
    (U : ι → V × V)
    (hU : ∀ (j : ι) (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = schrF P (s • U j) ⇑f → T g = T f)
    (a n : ℕ) : ∃ M : ℕ, ∀ N : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ (w : V × V)
      (h g : SchwartzMap V ℂ), ⇑g = schrF P w ⇑h →
      (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) ≤
        C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  classical
  obtain ⟨s₀, C₀, -, hT⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((SchwartzMap.seminorm ℂ a n).comp T.toLinearMap)
    (by exact ((schwartz_withSeminorms ℂ V₁ ℂ).continuous_seminorm (a, n)).comp T.continuous)
  obtain ⟨M, s₁, C₁, hC₁, hG⟩ := GlobalTheory.T.schrodinger_translation_seminorm_bound P hP s₀
  have uniq : ∀ {f g : 𝓢(V, ℂ)}, (⇑f : V → ℂ) = ⇑g → f = g := fun e => DFunLike.coe_injective e
  have ex : ∀ (w : V × V) (h : 𝓢(V, ℂ)), ∃ g : 𝓢(V, ℂ), ⇑g = schrF P w ⇑h :=
    fun w h => (hG w h).imp fun g hg => hg.1
  have mono : ∀ (t t' : Finset (ℕ × ℕ)), t ⊆ t' → ∀ f : 𝓢(V, ℂ),
      (t.sup (schwartzSeminormFamily ℂ V ℂ)) f ≤ (t'.sup (schwartzSeminormFamily ℂ V ℂ)) f :=
    fun t t' ht f => Seminorm.le_def.1 (Finset.sup_mono ht) f
  have base : ∀ (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h →
      SchwartzMap.seminorm ℂ a n (T g) ≤
        (C₀ * C₁) * (1 + ‖w‖) ^ M * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    intro w h g hg
    obtain ⟨g', hg', hb⟩ := hG w h
    obtain rfl : g' = g := uniq (hg'.trans hg.symm)
    have h1 : SchwartzMap.seminorm ℂ a n (T g') ≤
        (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g' := by
      have := Seminorm.le_def.1 hT g'
      rw [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at this
      exact this
    calc _ ≤ (C₀ : ℝ) * (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g' := h1
      _ ≤ (C₀ : ℝ) * (C₁ * (1 + ‖w‖) ^ M * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h) :=
          mul_le_mul_of_nonneg_left hb C₀.2
      _ = _ := by ring
  refine ⟨M, fun N => ?_⟩
  suffices key : ∀ N : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (w : V × V) (h g : 𝓢(V, ℂ)),
      ⇑g = schrF P w ⇑h → (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) ≤
        C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h by
    obtain ⟨s, C, -, hC⟩ := key N
    exact ⟨s, C, hC⟩
  intro N
  induction N with
  | zero => exact ⟨s₁, C₀ * C₁, mul_nonneg C₀.2 hC₁, fun w h g hg => by simpa using base w h g hg⟩
  | succ N ih =>
    obtain ⟨sN, CN, hCN, hN⟩ := ih
    choose sj Cj hCj hj using fun j => GlobalTheory.T.schrodinger_small_translation_continuity P hP (U j) sN
    let s' := sN ∪ Finset.univ.biUnion sj
    have perj : ∀ (j : ι) (w : V × V) (h g : 𝓢(V, ℂ)), ⇑g = schrF P w ⇑h →
        |omega P w (U j)| * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g)) ≤
          (CN / 2 + CN * Cj j / 4) * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
      intro j w h g hg
      have hX : 0 ≤ (1 + ‖w‖) ^ M := by positivity
      have hh : 0 ≤ (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := apply_nonneg _ _
      have hq : 0 ≤ SchwartzMap.seminorm ℂ a n (T g) := apply_nonneg _ _
      have hA : 0 ≤ (1 + ∑ j, |omega P w (U j)|) ^ N := by positivity
      have hCjj := hCj j
      have hsN := mono sN s' Finset.subset_union_left h
      by_cases hω : |omega P w (U j)| ≤ 1 / 2
      · have e1 := hN w h g hg
        have e2 : 0 ≤ CN * Cj j / 4 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
          positivity
        have e3 : CN * (1 + ‖w‖) ^ M * (sN.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
            CN * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by gcongr
        have e4 : |omega P w (U j)| * ((1 + ∑ j, |omega P w (U j)|) ^ N *
            SchwartzMap.seminorm ℂ a n (T g)) ≤ 1 / 2 * ((1 + ∑ j, |omega P w (U j)|) ^ N *
            SchwartzMap.seminorm ℂ a n (T g)) := mul_le_mul_of_nonneg_right hω (by positivity)
        nlinarith
      · push_neg at hω
        have hω0 : omega P w (U j) ≠ 0 := by
          intro h0; rw [h0, abs_zero] at hω; norm_num at hω
        set ω := omega P w (U j) with hωdef
        set t : ℝ := 1 / (2 * ω) with htdef
        have htω : t * ω = 1 / 2 := by rw [htdef]; field_simp
        have hat : |ω| * |t| = 1 / 2 := by rw [← abs_mul, mul_comm, htω]; norm_num
        have ht : |t| ≤ 1 := by
          by_contra hc; push_neg at hc
          have : (1 : ℝ) / 2 * 1 < |ω| * |t| := mul_lt_mul'' hω hc (by norm_num) (by norm_num)
          linarith
        obtain ⟨h', hh'⟩ := ex (t • U j) h
        obtain ⟨g₁, hg₁⟩ := ex w h'
        obtain ⟨gd, hgd⟩ := ex w (h' - h)
        have egd : gd = g₁ - g := uniq (by
          rw [hgd]; funext y
          rw [SchwartzMap.sub_apply, congrFun hg₁ y, congrFun hg y]
          simp [schrF, mul_sub])
        have e3 := GlobalTheory.T.schrodinger_invariant_operator_translate P hP T (U j) (hU j) w t h h' g g₁ hh' hg hg₁
        have hexp : Complex.exp (-(2 * Real.pi * Complex.I) * ((t * ω : ℝ) : ℂ)) = -1 := by
          rw [htω]; push_cast
          rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) = -(Real.pi * Complex.I) by ring,
            Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
        rw [hexp, neg_one_smul] at e3
        have eT : T gd = (-2 : ℂ) • T g := by
          rw [egd, map_sub, e3, neg_smul, two_smul]; abel
        have hqd : SchwartzMap.seminorm ℂ a n (T gd) = 2 * SchwartzMap.seminorm ℂ a n (T g) := by
          rw [eT, map_smul_eq_mul]; norm_num
        have hd := hj j t ht h h' hh'
        have hN' := hN w (h' - h) gd hgd
        have hsj : ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
            (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h :=
          mono _ _ ((Finset.subset_biUnion_of_mem sj (Finset.mem_univ j)).trans
            Finset.subset_union_right) h
        have hsupd : 0 ≤ (sN.sup (schwartzSeminormFamily ℂ V ℂ)) (h' - h) := apply_nonneg _ _
        calc |ω| * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g))
            = |ω| / 2 * ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T gd)) := by
              rw [hqd]; ring
          _ ≤ |ω| / 2 * (CN * (1 + ‖w‖) ^ M * (sN.sup (schwartzSeminormFamily ℂ V ℂ)) (h' - h)) := by
              gcongr
          _ ≤ |ω| / 2 * (CN * (1 + ‖w‖) ^ M *
                (Cj j * |t| * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h)) := by gcongr
          _ = CN * Cj j / 4 * (1 + ‖w‖) ^ M * ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h := by
              linear_combination (CN * (1 + ‖w‖) ^ M * Cj j *
                ((sj j).sup (schwartzSeminormFamily ℂ V ℂ)) h / 2) * hat
          _ ≤ CN * Cj j / 4 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
              gcongr
          _ ≤ _ := by
              have : 0 ≤ CN / 2 * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
                positivity
              nlinarith
    refine ⟨s', CN + ∑ j, (CN / 2 + CN * Cj j / 4), ?_, ?_⟩
    · have := fun j => hCj j
      have : 0 ≤ ∑ j, (CN / 2 + CN * Cj j / 4) :=
        Finset.sum_nonneg fun j _ => by have := hCj j; positivity
      linarith
    intro w h g hg
    calc (1 + ∑ j, |omega P w (U j)|) ^ (N + 1) * SchwartzMap.seminorm ℂ a n (T g)
        = (1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g) +
          ∑ j, |omega P w (U j)| *
            ((1 + ∑ j, |omega P w (U j)|) ^ N * SchwartzMap.seminorm ℂ a n (T g)) := by
          rw [pow_succ, ← Finset.sum_mul]; ring
      _ ≤ CN * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          ∑ j, (CN / 2 + CN * Cj j / 4) * (1 + ‖w‖) ^ M * (s'.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
          refine add_le_add ((hN w h g hg).trans ?_) (Finset.sum_le_sum fun j _ => perj j w h g hg)
          gcongr
          exact mono sN s' Finset.subset_union_left h
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

end GlobalTheory.ArchUniq
