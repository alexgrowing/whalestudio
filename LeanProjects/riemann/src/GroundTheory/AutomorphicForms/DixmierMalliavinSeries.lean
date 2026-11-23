import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contDiff_iteratedDeriv_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) :
    ∀ {Ψ : E × ℝ → F}, ContDiff ℝ ∞ Ψ → ∀ s : ℝ,
      ContDiff ℝ ∞ (fun Y : E => iteratedDeriv p (fun t : ℝ => Ψ (Y, t)) s) := by
  induction p with
  | zero =>
    intro Ψ hΨ s
    simp only [iteratedDeriv_zero]
    exact hΨ.comp (contDiff_id.prodMk contDiff_const)
  | succ p ih =>
    intro Ψ hΨ s
    have hd : ∀ Y : E, deriv (fun t : ℝ => Ψ (Y, t)) = fun t => fderiv ℝ Ψ (Y, t) (0, 1) := by
      intro Y; funext t
      have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (Y, t)) (Y, t) :=
        (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => ((Y, t) : E × ℝ)) (0, 1) t :=
        (hasDerivAt_const t Y).prodMk (hasDerivAt_id t)
      exact (h1.comp_hasDerivAt t h2).deriv
    have hΨ' : ContDiff ℝ ∞ (fun q : E × ℝ => fderiv ℝ Ψ q (0, 1)) :=
      (hΨ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have e : (fun Y : E => iteratedDeriv (p + 1) (fun t : ℝ => Ψ (Y, t)) s) =
        fun Y => iteratedDeriv p (fun t : ℝ => fderiv ℝ Ψ (Y, t) (0, 1)) s := by
      funext Y; rw [iteratedDeriv_succ', hd Y]
    rw [e]; exact ih hΨ' s

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def dirDeriv (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) : ℂ :=
  iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) 0

theorem iteratedDeriv_comp_expG_mul (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) (s : ℝ) :
    iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) s =
      h.dirDeriv X p f (h.expG (s • X) * x) := by
  have e := congrFun (iteratedDeriv_comp_add_const p (fun t : ℝ => f (h.expG (t • X) * x)) s) 0
  simp only [zero_add] at e
  rw [← e, dirDeriv]
  congr 1
  funext u
  rw [h.expG_add_smul, mul_assoc]

theorem contMDiff_expG_smul_mul (X : 𝔤) (x : G) :
    letI := h.chartedSpace; ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔤) ∞ (fun t : ℝ => h.expG (t • X) * x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  exact (h.contMDiff_expG_comp (contDiff_id.smul contDiff_const)).mul contMDiff_const

theorem contDiff_comp_expG_smul_mul {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (x : G) :
    ContDiff ℝ ∞ (fun t : ℝ => f (h.expG (t • X) * x)) := by
  let := h.chartedSpace
  exact (hf.comp (h.contMDiff_expG_smul_mul X x)).contDiff

theorem contDiff_comp_expG_smul_mul_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (g : G) :
    ContDiff ℝ ∞ (fun q : 𝔤 × ℝ => f (h.expG (q.2 • X) * (g * h.expG q.1))) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × ℝ) 𝓘(ℝ, 𝔤) ∞
      (fun q : 𝔤 × ℝ => h.expG (q.2 • X) * (g * h.expG q.1)) :=
    (h.contMDiff_expG_comp (contDiff_snd.smul contDiff_const)).mul
      (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst))
  exact (hf.comp hm).contDiff

theorem dirDeriv_eq_zero_of_notMem {f : G → ℂ} (X : 𝔤) (p : ℕ) {x : G}
    (hx : x ∉ tsupport f) : h.dirDeriv X p f x = 0 := by
  have hc : Continuous (fun t : ℝ => h.expG (t • X) * x) :=
    (h.continuous_expG.comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h.expG ((0 : ℝ) • X) * x = x := by
    simp only [zero_smul]; rw [h.expG_zero, one_mul]
  have hev : (fun t : ℝ => f (h.expG (t • X) * x)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have := hc.continuousAt (x := 0)
    rw [ContinuousAt] at this
    simp only [h0] at this
    exact this.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)
  rw [dirDeriv, hev.iteratedDeriv_eq]
  simp

theorem contDiff_dirDeriv_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (p : ℕ) (g : G) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => h.dirDeriv X p f (g * h.expG Y)) :=
  contDiff_iteratedDeriv_snd p (h.contDiff_comp_expG_smul_mul_mul_expG hf X g) 0

theorem mem_chart_source_self (g : G) : g ∈ (h.chart g).source := by
  let := h.chartedSpace
  exact mem_chart_source 𝔤 g

theorem chart_symm_chart {g x : G} (hx : x ∈ (h.chart g).source) :
    g * h.expG (h.chart g x) = x :=
  (h.chart g).left_inv hx

theorem exists_bound_dirDeriv {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) :
    ∃ M : ℕ → ℝ, (∀ p x, ‖h.dirDeriv X p f x‖ ≤ M p) ∧
      ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) →
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞
          (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x)) ∧
        HasCompactSupport (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  let U : G → Set G := fun g => (h.chart g).source ∩ (h.chart g) ⁻¹' Metric.ball 0 1
  have hU : ∀ g, IsOpen (U g) := fun g =>
    (h.chart g).isOpen_inter_preimage Metric.isOpen_ball
  have hgU : ∀ g, g ∈ U g := fun g =>
    ⟨h.mem_chart_source_self g, by
      show h.chart g g ∈ Metric.ball 0 1
      rw [h.chart_self]; exact Metric.mem_ball_self one_pos⟩
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover U (fun g _ => (hU g).mem_nhds (hgU g))
  let β : ContDiffBump (0 : 𝔤) := ⟨1, 2, one_pos, one_lt_two⟩
  let Φ : G → ℕ → 𝔤 → ℂ := fun g p Y => (β Y : ℂ) * h.dirDeriv X p f (g * h.expG Y)
  have hΦ : ∀ g p, ContDiff ℝ ∞ (Φ g p) := fun g p =>
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul (h.contDiff_dirDeriv_mul_expG hf X p g)
  have hΦc : ∀ g p, HasCompactSupport (Φ g p) := fun g p =>
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hS : ∀ g k p, ∃ C, ∀ Y, ‖iteratedFDeriv ℝ k (Φ g p) Y‖ ≤ C := fun g k p =>
    ((hΦ g p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((hΦc g p).iteratedFDeriv k)
  choose S hS using hS
  have hS0 : ∀ g k p, 0 ≤ S g k p := fun g k p => (norm_nonneg _).trans (hS g k p 0)
  let M : ℕ → ℝ := fun p => ∑ g ∈ t, ∑ k ∈ Finset.range (p + 1), S g k p
  have hM0 : ∀ p, 0 ≤ M p := fun p =>
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p
  have hSM : ∀ p, ∀ g ∈ t, ∀ k ≤ p, S g k p ≤ M p := by
    intro p g hg k hk
    calc S g k p ≤ ∑ k ∈ Finset.range (p + 1), S g k p :=
          Finset.single_le_sum (fun k _ => hS0 g k p) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
      _ ≤ M p := Finset.single_le_sum (f := fun g => ∑ k ∈ Finset.range (p + 1), S g k p)
          (fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p) hg

  have hloc : ∀ g p x, x ∈ U g → h.dirDeriv X p f x = Φ g p (h.chart g x) := by
    intro g p x hx
    have hb : β (h.chart g x) = 1 :=
      β.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.2)
    simp only [Φ, hb, Complex.ofReal_one, one_mul, h.chart_symm_chart hx.1]
  have hzero : ∀ p x, x ∉ K → h.dirDeriv X p f x = 0 := fun p x hx =>
    h.dirDeriv_eq_zero_of_notMem X p hx
  refine ⟨M, ?_, ?_⟩
  · intro p x
    by_cases hx : x ∈ K
    · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
      rw [hloc g p x hxg]
      calc ‖Φ g p (h.chart g x)‖ = ‖iteratedFDeriv ℝ 0 (Φ g p) (h.chart g x)‖ := by
            rw [norm_iteratedFDeriv_zero]
        _ ≤ S g 0 p := hS g 0 p _
        _ ≤ M p := hSM p g hg 0 (Nat.zero_le p)
    · rw [hzero p x hx, norm_zero]; exact hM0 p
  intro c hc

  let F : G → 𝔤 → ℂ := fun g Y => ∑' p, (c p) • Φ g p Y
  have hF : ∀ g ∈ t, ContDiff ℝ ∞ (F g) := by
    intro g hg
    refine contDiff_tsum (N := ⊤) (v := fun k p => |c p| * S g k p)
      (fun p => (hΦ g p).const_smul (c p)) ?_ ?_
    · intro k _
      rw [← summable_nat_add_iff k]
      refine Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (hS0 g k _))
        (fun p => mul_le_mul_of_nonneg_left (hSM (p + k) g hg k (Nat.le_add_left k p))
          (abs_nonneg _)) ?_
      exact (summable_nat_add_iff k).2 hc
    · intro k p Y _
      rw [iteratedFDeriv_const_smul_apply' ((hΦ g p).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hS g k p Y) (abs_nonneg _)
  have hsupp : ∀ x, x ∉ K → ∑' p, (c p : ℂ) * h.dirDeriv X p f x = 0 := by
    intro x hx; simp [hzero _ x hx]
  refine ⟨?_, HasCompactSupport.intro hK hsupp⟩
  intro x
  by_cases hx : x ∈ K
  · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
    have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x]
        fun x => F g (chartAt 𝔤 g x) := by
      filter_upwards [(hU g).mem_nhds hxg] with x' hx'
      show _ = F g (h.chart g x')
      simp only [F, hloc g _ x' hx', Complex.real_smul]
    have hch : ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ (chartAt 𝔤 g) x := by
      have := contMDiffAt_extChartAt' (I := 𝓘(ℝ, 𝔤)) (n := ∞) (x := g) hxg.1
      simpa [extChartAt] using this
    exact (((hF g hg).contMDiff.contMDiffAt).comp x hch).congr_of_eventuallyEq hev
  · have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with x' hx'
      exact hsupp x' hx'
    exact contMDiffAt_const.congr_of_eventuallyEq hev

end IsExpLieAlgebra

end GroundTheory.Automorphic
