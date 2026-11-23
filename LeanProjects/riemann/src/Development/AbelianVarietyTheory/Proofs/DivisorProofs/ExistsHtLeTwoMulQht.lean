import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.CuspDbl

open Metric

theorem removable_param {Y : Type} [TopologicalSpace Y] {G H : ℂ → Y → ℂ} {s₀ : ℂ} {r : ℝ} {k : ℕ} {B : Y → ℝ} (hr : 0 < r)
    (hGH : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ y, H s y = (s - s₀) ^ k * G s y)
    (hd : ∀ y, DifferentiableOn ℂ (fun s => H s y) (ball s₀ r))
    (hc : ContinuousOn (fun x : ℂ × Y => H x.1 x.2) (ball s₀ r ×ˢ Set.univ))
    (hB : ∀ s ∈ ball s₀ r, ∀ y, ‖H s y‖ ≤ B y) (h₀ : ∀ y, ContinuousAt (fun s => G s y) s₀) :
    (∀ y, DifferentiableOn ℂ (fun s => G s y) (ball s₀ r)) ∧ (∀ s ∈ ball s₀ (r / 2), Continuous (G s)) ∧
      ∀ s ∈ ball s₀ (r / 2), ∀ y, ‖G s y‖ ≤ B y / (r / 2) ^ k := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hG : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ y, G s y = H s y / (s - s₀) ^ k := fun s hs hne y => by
    rw [hGH s hs hne y, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 hne))]
  have hGd : ∀ y, DifferentiableOn ℂ (fun s => G s y) (ball s₀ r) := fun y => by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds s₀ hr)).1 ⟨?_, h₀ y⟩
    refine DifferentiableOn.congr (f := fun s => H s y / (s - s₀) ^ k) ?_ fun s hs => hG s hs.1 hs.2 y
    exact ((hd y).mono Set.diff_subset).div (by fun_prop) fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs.2)
  have hsub : closedBall s₀ (r / 2) ⊆ ball s₀ r := closedBall_subset_ball (half_lt_self hr)
  have hsph : ∀ s ∈ sphere s₀ (r / 2), s ∈ ball s₀ r ∧ s ≠ s₀ ∧ ‖s - s₀‖ = r / 2 := fun s hs =>
    ⟨hsub (sphere_subset_closedBall hs), ne_of_mem_sphere hs hr2.ne', mem_sphere_iff_norm.1 hs⟩
  have hmax : ∀ {u : ℂ → ℂ} {c : ℝ}, DifferentiableOn ℂ u (ball s₀ r) → (∀ s ∈ sphere s₀ (r / 2), ‖u s‖ ≤ c) →
      ∀ s ∈ ball s₀ (r / 2), ‖u s‖ ≤ c := fun {u c} hu hb s hs => by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (DifferentiableOn.diffContOnCl_ball hu hsub) (fun z hz => hb z ?_) (subset_closure hs)
    rwa [frontier_ball s₀ hr2.ne'] at hz
  refine ⟨hGd, fun s hs => continuous_iff_continuousAt.2 fun y₀ => ?_, fun s hs y => hmax (hGd y) (fun z hz => ?_) s hs⟩
  · refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have h1 : ∀ᶠ y in 𝓝 y₀, ∀ z ∈ sphere s₀ (r / 2), ‖H z y - H z y₀‖ < ε / 2 * (r / 2) ^ k := by
      refine (isCompact_sphere s₀ (r / 2)).eventually_forall_of_forall_eventually fun z hz => ?_
      have h2 : ContinuousAt (fun x : ℂ × Y => H x.1 x.2) (z, y₀) :=
        hc.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨(hsph z hz).1, trivial⟩)
      have h3 : ContinuousAt (fun x : Y × ℂ => ‖H x.2 x.1 - H x.2 y₀‖) (y₀, z) :=
        ((h2.comp_of_eq (f := fun x : Y × ℂ => (x.2, x.1)) (by fun_prop) rfl).sub
          (h2.comp_of_eq (f := fun x : Y × ℂ => (x.2, y₀)) (by fun_prop) rfl)).norm
      exact h3.eventually_lt continuousAt_const (by simp only [sub_self, norm_zero]; positivity)
    filter_upwards [h1] with y hy
    rw [dist_eq_norm]
    refine (hmax (c := ε / 2) ((hGd y).sub (hGd y₀)) (fun z hz => ?_) s hs).trans_lt (half_lt_self hε)
    obtain ⟨a, b, c⟩ := hsph z hz
    simp only [Pi.sub_apply]
    rw [hG z a b, hG z a b, ← sub_div, norm_div, norm_pow, c, div_le_iff₀ (by positivity)]
    exact (hy z hz).le
  · obtain ⟨a, b, c⟩ := hsph z hz
    rw [hG z a b, norm_div, norm_pow, c]
    exact div_le_div_of_nonneg_right (hB z a y) (by positivity)

theorem local_form {Y : Type} [TopologicalSpace Y] {ht : Y → ℝ} (hht : ∀ y, 0 ≤ ht y) {Ei e : ℂ → Y → ℂ} {σ₀ : ℝ}
    (hE : ∀ s : ℂ, σ₀ < s.re → ∀ y, Ei s y = e s y)
    (hloc : ∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → Y → ℂ), 0 < r ∧
        (∀ s ∈ ball s₁ r, s ≠ s₁ → ∀ y, H s y = (s - s₁) ^ k * Ei s y) ∧
        (∀ y, DifferentiableOn ℂ (fun s => H s y) (ball s₁ r)) ∧
        ContinuousOn (fun x : ℂ × Y => H x.1 x.2) (ball s₁ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₁ r, ∀ y, ‖H s y‖ ≤ C * ht y ^ N)
    {s₀ : ℂ} {Ψ : Y → ℂ} (hΨ : ∀ y, GlobalTheory.Cont.HolValueAt (fun s => e s y) s₀ (Ψ y)) (s₁ : ℂ) :
    ∃ (k : ℕ) (r C : ℝ) (N : ℕ) (H : ℂ → Y → ℂ), 0 < r ∧ 0 ≤ C ∧ (s₁ = s₀ → k = 0) ∧
      (∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → ∀ y, H s y = (s - s₁) ^ k * (if s = s₀ then Ψ y else Ei s y)) ∧
      (∀ y, DifferentiableOn ℂ (fun s => H s y) (ball s₁ r)) ∧ (∀ s ∈ ball s₁ r, Continuous (H s)) ∧
      (∀ s ∈ ball s₁ r, ∀ y, ‖H s y‖ ≤ C * ht y ^ N) ∧
      ∀ y y', (∀ s : ℂ, σ₀ < s.re → e s y = e s y') → ∀ s ∈ ball s₁ r, H s y = H s y' := by
  have hm : ∀ y, GlobalTheory.Cont.IsMerExt (fun s => e s y) Set.univ fun s => Ei s y := fun y => by
    refine GlobalTheory.Cont.isMerExt_univ.2 ⟨fun x => ?_, σ₀, fun s hs => hE s hs y⟩
    obtain ⟨k, r, H, hr, h1, h2, -⟩ := hloc x
    have h3 : MeromorphicAt (fun s => H s y / (s - x) ^ k) x :=
      ((h2 y).analyticAt (ball_mem_nhds x hr)).meromorphicAt.fun_div (by fun_prop)
    refine h3.congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), self_mem_nhdsWithin] with s hs hne
    rw [h1 s hs hne y, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 hne))]
  suffices h : ∃ (k : ℕ) (r C : ℝ) (N : ℕ) (H : ℂ → Y → ℂ), 0 < r ∧ 0 ≤ C ∧ (s₁ = s₀ → k = 0) ∧
      (∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → ∀ y, H s y = (s - s₁) ^ k * (if s = s₀ then Ψ y else Ei s y)) ∧
      (∀ y, DifferentiableOn ℂ (fun s => H s y) (ball s₁ r)) ∧ (∀ s ∈ ball s₁ r, Continuous (H s)) ∧
      (∀ s ∈ ball s₁ r, ∀ y, ‖H s y‖ ≤ C * ht y ^ N) by
    obtain ⟨k, r, C, N, H, hr, hC, hk, h1, h2, h3, h4⟩ := h
    refine ⟨k, r, C, N, H, hr, hC, hk, h1, h2, h3, h4, fun y y' hy => ?_⟩
    have h5 : (fun s => Ei s y) =ᶠ[𝓝[≠] s₁] fun s => Ei s y' :=
      (((hm y).isExtAt trivial).congr ⟨σ₀, fun s hs => hy s hs⟩).eventuallyEq ((hm y').isExtAt trivial)
    have h6 : Ψ y = Ψ y' := ((hΨ y).congr ⟨σ₀, fun s hs => hy s hs⟩).unique (hΨ y')
    refine ((h2 y).analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq ((h2 y').analyticOnNhd isOpen_ball)
      (convex_ball s₁ r).isPreconnected (mem_ball_self hr) (Eventually.frequently ?_)
    filter_upwards [h5, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr), self_mem_nhdsWithin] with s a b c
    rw [h1 s b (.inl c), h1 s b (.inl c), a, h6]
  obtain ⟨k, r, H, hr, h1, h2, h3, C, N, h4⟩ := hloc s₁
  have h4' : ∀ s ∈ ball s₁ r, ∀ y, ‖H s y‖ ≤ |C| * ht y ^ N := fun s hs y =>
    (h4 s hs y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (hht y) N))
  by_cases h0 : s₁ = s₀
  · subst h0
    obtain ⟨a, b, c⟩ := removable_param (G := fun s y => if s = s₁ then Ψ y else Ei s y) hr
      (fun s hs hne y => by simp only [if_neg hne]; exact h1 s hs hne y) h2 h3 h4' fun y => by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
        simp only [if_true]
        refine (((hm y).isExtAt trivial).holValueAt_iff.1 (hΨ y)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [if_neg (show s ≠ s₁ from hs)]
    refine ⟨0, r / 2, |C| / (r / 2) ^ k, N, fun s y => if s = s₁ then Ψ y else Ei s y, half_pos hr, by positivity,
      fun _ => rfl, fun s _ _ y => by simp, fun y => (a y).mono (ball_subset_ball (half_le_self hr.le)), b,
      fun s hs y => (c s hs y).trans_eq (by ring)⟩
  · have hρ : 0 < min r (dist s₀ s₁) := lt_min hr (dist_pos.2 (Ne.symm h0))
    have hsub : ball s₁ (min r (dist s₀ s₁)) ⊆ ball s₁ r := ball_subset_ball (min_le_left _ _)
    refine ⟨k + 1, min r (dist s₀ s₁), r * |C|, N, fun s y => (s - s₁) * H s y, hρ, by positivity, fun h => absurd h h0,
      fun s hs hne y => ?_, fun y => DifferentiableOn.fun_mul (by fun_prop) ((h2 y).mono hsub), fun s hs => ?_,
      fun s hs y => ?_⟩
    · have hne' : s ≠ s₁ := hne.resolve_right (Nat.succ_ne_zero k)
      have hs0 : s ≠ s₀ := by
        rintro rfl
        exact absurd (mem_ball.1 hs) (not_lt.2 (min_le_right _ _))
      simp only [if_neg hs0, h1 s (hsub hs) hne' y]
      ring
    · refine continuous_const.mul ?_
      exact h3.comp_continuous (f := fun y => (s, y)) (by fun_prop) fun y => ⟨hsub hs, trivial⟩
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul (mem_ball_iff_norm.1 (hsub hs)).le (h4' s (hsub hs) y) (norm_nonneg _) hr.le

theorem exists_ht_le_two_mul_qht {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) :
    ∃ γ ∈ ratU σ J, ht (γ * h) ≤ 2 * qht h := by
  have h1 : 1 ≤ qht h := le_ciInf fun γ => one_le_heightGL F _
  have h2 : qht h < 2 * qht h := lt_two_mul_self (one_pos.trans_le h1)
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h2
  exact ⟨γ.1, γ.2, hγ.le⟩

theorem isRegFam_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (W : Spc F E n)
    (W₂ : Spc F E (n + n)), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ f : ℂ → UA σ W₂.J → ℂ, (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (f s) ∧ ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (f s) g) →
    ∀ Ei : ℂ → UA σ W₂.J → ℂ, (∀ s : ℂ, (n : ℝ) / 2 < s.re → ∀ g, Ei s g = GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (f s) g) →
    (∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → UA σ W₂.J → ℂ), 0 < r ∧
        (∀ s ∈ Metric.ball s₁ r, s ≠ s₁ → ∀ g, H s g = (s - s₁) ^ k * Ei s g) ∧
        (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₁ r)) ∧
        ContinuousOn (fun x : ℂ × UA σ W₂.J => H x.1 x.2) (Metric.ball s₁ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₁ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N) →
    ∀ (s₀ : ℂ) (Ψ : UA σ W₂.J → ℂ), (∀ g, GlobalTheory.Cont.HolValueAt (fun s => GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (f s) g) s₀ (Ψ g)) →
    ∀ w : UA σ W.J → ℂ, Continuous w → (∀ x, ‖w x‖ = 1) → (∀ γ ∈ ratU σ W.J, ∀ x, w (γ * x) = w x) →
      GlobalTheory.CuspDbl.IsRegFam (fun h : UA σ W.J => (qht h : ℝ)) s₀
        (fun s h h' => (if s = s₀ then Ψ (i (h, h')) else Ei s (i (h, h'))) * w h') := by
  intro F E _ _ _ _ _ σ n W W₂ _ i hi f hf Ei hEi hloc s₀ Ψ hΨ w hwc hw1 _ s₁
  have hi' : ∀ h h', (i (h, h')).1 = blkGL finSumFinEquiv (h.1, h'.1) := fun h h' => Units.ext (hi h h')
  have hic : Continuous i := continuous_induced_rng.2 (((continuous_blkGL finSumFinEquiv).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))).congr
      fun x => (hi' x.1 x.2).symm)
  have hrat : ∀ γ ∈ ratU σ W.J, ∀ γ' ∈ ratU σ W.J, i (γ, γ') ∈ ratU σ W₂.J := fun γ hγ γ' hγ' => by
    rw [ratU, Subgroup.mem_subgroupOf] at hγ hγ' ⊢
    obtain ⟨A, hA⟩ := hγ
    obtain ⟨A', hA'⟩ := hγ'
    refine ⟨blkGL finSumFinEquiv (A, A'), Units.ext ?_⟩
    change (blkMat finSumFinEquiv A.1 A'.1).map _ = mat (i (γ, γ'))
    rw [hi, blkMat_map _ _ (map_zero _)]
    have h1 : (A.1).map (inclR (F := F) (E := E) (AF F)) = mat γ := congrArg Units.val hA
    have h2 : (A'.1).map (inclR (F := F) (E := E) (AF F)) = mat γ' := congrArg Units.val hA'
    rw [h1, h2]
  have hht : ∀ h h', ht (i (h, h')) ≤ ht h * ht h' := fun h h' => by
    unfold ht
    rw [hi']
    exact GlobalTheory.BlockHeight.heightGL_blk_le F finSumFinEquiv _ _ _ rfl rfl
  obtain ⟨k, r, C, N, H, hr, hC, hk, h1, h2, h3, h4, h5⟩ :=
    local_form (ht := fun g : UA σ W₂.J => (ht g : ℝ)) (fun g => (ht g).2) hEi hloc hΨ s₁
  refine ⟨k, r, C * 4 ^ N, N, fun s h h' => H s (i (h, h')) * w h', hr, hk, fun s hs hne h h' => ?_,
    fun h h' => (h2 _).mul_const _, fun s hs => ((h3 s hs).comp hic).mul (hwc.comp continuous_snd), fun s hs h h' => ?_⟩
  · simp only [h1 s hs hne, mul_assoc]
  · obtain ⟨γ, hγ, a⟩ := exists_ht_le_two_mul_qht h
    obtain ⟨γ', hγ', a'⟩ := exists_ht_le_two_mul_qht h'
    have e : H s (i (γ * h, γ' * h')) = H s (i (h, h')) := by
      refine h5 _ _ (fun t ht => ?_) s hs
      rw [← Prod.mk_mul_mk, map_mul]
      exact GlobalTheory.Eis.leftInv_cosetSum (hf t ht).1 _ (hrat γ hγ γ' hγ') _
    have b : ht (i (γ * h, γ' * h')) ≤ 4 * (qht h * qht h') :=
      (hht _ _).trans ((mul_le_mul' a a').trans_eq (by ring))
    have b' : (ht (i (γ * h, γ' * h')) : ℝ) ≤ 4 * ((qht h : ℝ) * (qht h' : ℝ)) := by exact_mod_cast b
    rw [norm_mul, hw1, mul_one, ← e, mul_assoc, ← mul_pow]
    exact (h4 s hs _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ht _).2 b' N) hC)

end GlobalTheory.CuspDbl

end
