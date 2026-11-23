import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedFDerivSubApply

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal

section General

variable {S : Type} [AddCommGroup S] [Module ℂ S]

theorem norming (q : Seminorm ℂ S) (g : S) : ∃ T : S →ₗ[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg], fun x => by simp⟩
  let f : Module.Dual ℂ (Submodule.span ℂ {g}) := (q g : ℂ) • (LinearEquiv.coord ℂ S g hg).toLinearMap
  have hf : ∀ x : Submodule.span ℂ {g}, ‖f x‖ ≤ q x := fun x => by
    have h := LinearEquiv.coord_apply_smul ℂ S g hg x
    have : q x = ‖LinearEquiv.coord ℂ S g hg x‖ * q g := by rw [← map_smul_eq_mul, h]
    rw [this]
    simp [f, mul_comm, abs_of_nonneg (apply_nonneg q g)]
  obtain ⟨T, hT, hle⟩ := Module.Dual.exists_extension_of_le_seminorm _ f hf
  refine ⟨T, ?_, hle⟩
  have := hT ⟨g, Submodule.mem_span_singleton_self g⟩
  simp only at this
  rw [this]
  simp [f, abs_of_nonneg (apply_nonneg q g), LinearEquiv.coord_self]

variable [TopologicalSpace S] [IsTopologicalAddGroup S]

def toCLM (q : Seminorm ℂ S) (hq : Continuous q) (T : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ x, ‖T x‖ ≤ C * q x) : S →L[ℂ] ℂ :=
  ⟨T, continuous_of_continuousAt_zero T (by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm h ?_
    have := (hq.tendsto 0).const_mul C
    simpa using this)⟩

theorem norming' (q : Seminorm ℂ S) (hq : Continuous q) (g : S) : ∃ T : S →L[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by
  obtain ⟨T, h1, h2⟩ := norming q g
  exact ⟨toCLM q hq T 1 (by simpa using h2), h1, h2⟩

def Sy (_ : Seminorm ℂ S) : Type := S

instance (q : Seminorm ℂ S) : AddCommGroup (Sy q) := inferInstanceAs (AddCommGroup S)
instance (q : Seminorm ℂ S) : Module ℂ (Sy q) := inferInstanceAs (Module ℂ S)
instance (q : Seminorm ℂ S) : SeminormedAddCommGroup (Sy q) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := Sy q) q.toAddGroupSeminorm
instance (q : Seminorm ℂ S) : NormedSpace ℂ (Sy q) := ⟨fun a x => (map_smul_eq_mul q a x).le⟩

theorem weak_bounded {ι : Type} (g : ι → S) (h : ∀ T : S →L[ℂ] ℂ, ∃ C, ∀ i, ‖T (g i)‖ ≤ C) (q : Seminorm ℂ S) (hq : Continuous q) :
    ∃ C, ∀ i, q (g i) ≤ C := by
  let e : ι → (Sy q →L[ℂ] ℂ) →L[ℂ] ℂ := fun i => ContinuousLinearMap.apply ℂ ℂ (g i : Sy q)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := e) fun f =>
    h (toCLM q hq (f : Sy q →ₗ[ℂ] ℂ) ‖f‖ fun x => f.le_opNorm x)
  refine ⟨max C 0, fun i => ?_⟩
  obtain ⟨T, h1, h2⟩ := norming q (g i)
  let f : Sy q →L[ℂ] ℂ := LinearMap.mkContinuous (E := Sy q) T 1 fun x => by rw [one_mul]; exact h2 x
  have hf : ‖f‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc q (g i) = ‖e i f‖ := h1.symm
    _ ≤ ‖e i‖ * ‖f‖ := (e i).le_opNorm f
    _ ≤ max C 0 * 1 := mul_le_mul ((hC i).trans (le_max_left _ _)) hf (norm_nonneg _) (le_max_right _ _)
    _ = _ := mul_one _

end General

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

theorem equicont {ι : Type} (T : ι → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) (q : Seminorm ℂ 𝓢(V₁, ℂ)) (hq : Continuous q)
    (h : ∀ f, ∃ C, ∀ i, q (T i f) ≤ C) : ∃ p : Seminorm ℂ 𝓢(V, ℂ), Continuous p ∧ ∀ i f, q (T i f) ≤ p f := by
  haveI := GlobalTheory.CompanionTheory.SchwartzBaire.baireSpace (E := V) (F := ℂ)
  have hb : BddAbove (range fun i => q.comp (T i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨C, hC⟩ := h f
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩
  refine ⟨⨆ i, q.comp (T i).toLinearMap, ?_, fun i f => ?_⟩
  · rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup (fun i => q.comp (T i).toLinearMap) (fun i => hq.comp (T i).continuous) hb
  exact (le_ciSup hb i : q.comp (T i).toLinearMap ≤ _) f

theorem cont_seminorm (k n : ℕ) : Continuous (SchwartzMap.seminorm ℂ k n : 𝓢(V, ℂ) → ℝ) :=
  (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)

def derAt (n : ℕ) (x : V) : 𝓢(V, ℂ) →L[ℂ] (V [×n]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => iteratedFDeriv ℝ n f x)
    (fun f g => by
      have hf : ContDiff ℝ n f := f.smooth'.of_le (by exact_mod_cast le_top)
      have hg : ContDiff ℝ n g := g.smooth'.of_le (by exact_mod_cast le_top)
      exact iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt)
    (fun a f => by
      have hf : ContDiff ℝ n f := f.smooth'.of_le (by exact_mod_cast le_top)
      exact iteratedFDeriv_const_smul_apply hf.contDiffAt)
    ⟨{(0, n)}, 1, zero_le_one, fun f => by simpa using f.norm_iteratedFDeriv_le_seminorm ℂ n x⟩

theorem strong_of_weak [FiniteDimensional ℝ V] {K : Type} [TopologicalSpace K] (g : K → 𝓢(V, ℂ))
    (hw : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun k => T (g k))
    (hb : ∀ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q → ∃ C, ∀ k, q (g k) ≤ C) : Continuous g := by
  have hd : ∀ n x, Continuous fun k => iteratedFDeriv ℝ n (g k) x := fun n x => by
    haveI : Module.Finite ℝ (V [×n]→L[ℝ] ℂ) :=
      Module.Finite.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
        ContinuousMultilinearMap.toMultilinearMap_injective
    haveI : Module.Finite ℂ (V [×n]→L[ℝ] ℂ) := Module.Finite.of_restrictScalars_finite ℝ ℂ _
    let b := (Module.finBasis ℂ (V [×n]→L[ℝ] ℂ)).equivFunL
    have : Continuous fun k => b (derAt n x (g k)) := continuous_pi fun i =>
      hw ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) i).comp (b.toContinuousLinearMap.comp (derAt n x)))
    refine (b.symm.continuous.comp this).congr fun k => ?_
    exact b.symm_apply_apply _
  refine continuous_iff_continuousAt.2 fun k₀ => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨j, n⟩ ε hε
  obtain ⟨C₁, h₁⟩ := hb _ (cont_seminorm (j + 1) n)
  obtain ⟨C₂, h₂⟩ := hb _ (cont_seminorm 0 (n + 1))
  have c₁ : 0 ≤ C₁ := (apply_nonneg _ _).trans (h₁ k₀)
  have c₂ : 0 ≤ C₂ := (apply_nonneg _ _).trans (h₂ k₀)
  set R : ℝ := 4 * C₁ / ε + 1 with hR
  have R1 : 1 ≤ R := by have : 0 ≤ 4 * C₁ / ε := by positivity
                        linarith
  set η : ℝ := ε / 4 / R ^ j with hη
  have η0 : 0 < η := by positivity
  set δ : ℝ := η / (2 * C₂ + 1) with hδ
  have δ0 : 0 < δ := by positivity
  obtain ⟨t, -, tf, ht⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : V) R) δ0
  have hev : ∀ᶠ k in 𝓝 k₀, ∀ x ∈ t, ‖iteratedFDeriv ℝ n (g k - g k₀) x‖ < η := by
    rw [eventually_all_finite tf]
    intro x _
    have := ((hd n x).tendsto k₀).eventually (Metric.ball_mem_nhds _ η0)
    filter_upwards [this] with k hk
    have e := GlobalTheory.CompanionTheory.SchwartzBaire.iteratedFDeriv_sub_apply' (g k) (g k₀) n x
    rw [e, ← dist_eq_norm]
    exact hk
  filter_upwards [hev] with k hk
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ j n _ (half_pos hε).le fun x => ?_) (half_lt_self hε)
  have s1 : ∀ a b, SchwartzMap.seminorm ℂ a b (g k - g k₀) ≤
      SchwartzMap.seminorm ℂ a b (g k) + SchwartzMap.seminorm ℂ a b (g k₀) := fun a b => map_sub_le_add _ _ _
  by_cases hx : ‖x‖ ≤ R
  · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_closedBall_zero_iff.2 hx))
    have hs : ContDiff ℝ (n + 1 : ℕ) (g k - g k₀ : 𝓢(V, ℂ)) := (g k - g k₀).smooth'.of_le (by exact_mod_cast le_top)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ))) :=
      hs.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hl := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (C := 2 * C₂)
      (fun z _ => hdiff z) (fun z _ => by
        rw [norm_fderiv_iteratedFDeriv]
        have := (g k - g k₀).norm_iteratedFDeriv_le_seminorm ℂ (n + 1) z
        linarith [s1 0 (n + 1), h₂ k, h₂ k₀]) convex_univ (mem_univ y) (mem_univ x)
    have hd' : ‖x - y‖ ≤ δ := by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hxy).le
    have e1 : 2 * C₂ * ‖x - y‖ ≤ η := by
      calc 2 * C₂ * ‖x - y‖ ≤ (2 * C₂ + 1) * δ := by gcongr; linarith
        _ = η := by rw [hδ]; field_simp
    have e2 : ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖ ≤ 2 * η := by
      have := norm_le_insert' (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x) (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) y)
      have h3 : ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) y‖ < η := hk y hy
      linarith
    calc ‖x‖ ^ j * ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖ ≤ R ^ j * (2 * η) := by gcongr
      _ = ε / 2 := by rw [hη]; field_simp; ring
  · push Not at hx
    have h4 := (g k - g k₀).le_seminorm ℂ (j + 1) n x
    have h5 : ‖x‖ * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖) ≤ 2 * C₁ := by
      rw [← mul_assoc, ← pow_succ']
      linarith [s1 (j + 1) n, h₁ k, h₁ k₀]
    have h6 : 2 * C₁ ≤ ‖x‖ * (ε / 2) := by
      have : 4 * C₁ / ε ≤ ‖x‖ := by linarith
      rw [div_le_iff₀ hε] at this
      linarith
    exact le_of_mul_le_mul_left (h5.trans h6) (by linarith)

def evAt (x : V) : 𝓢(V, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f x) (fun _ _ => rfl) (fun _ _ => rfl)
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by simpa using f.norm_le_seminorm ℂ x⟩

theorem evAt_apply (x : V) (f : 𝓢(V, ℂ)) : evAt x f = f x := rfl

theorem eq_of_weak {f g : 𝓢(V, ℂ)} (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, T f = T g) : f = g :=
  SchwartzMap.ext fun x => h (evAt x)

theorem weak_op {α : Type} [MeasurableSpace α] (μ : Measure α) (G : α → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ))
    (hex : ∀ f, ∃ g : 𝓢(V₁, ℂ), ∀ T : 𝓢(V₁, ℂ) →L[ℂ] ℂ, Integrable (fun a => T (G a f)) μ ∧ T g = ∫ a, T (G a f) ∂μ)
    (hb : ∀ k j : ℕ, ∃ (p : Seminorm ℂ 𝓢(V, ℂ)) (h : α → ℝ), Continuous p ∧ Integrable h μ ∧
      ∀ a f, SchwartzMap.seminorm ℂ k j (G a f) ≤ p f * h a) :
    ∃ L : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ), ∀ f (T : 𝓢(V₁, ℂ) →L[ℂ] ℂ), Integrable (fun a => T (G a f)) μ ∧ T (L f) = ∫ a, T (G a f) ∂μ := by
  choose g hg using hex
  let L : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V₁, ℂ) :=
    { toFun := g
      map_add' := fun a b => eq_of_weak fun T => by
        rw [map_add, (hg _ T).2, (hg _ T).2, (hg _ T).2, ← integral_add (hg _ T).1 (hg _ T).1]
        simp
      map_smul' := fun c a => eq_of_weak fun T => by
        rw [map_smul, (hg _ T).2, (hg _ T).2, ← integral_smul]
        simp }
  refine ⟨⟨L, ?_⟩, hg⟩
  refine (schwartz_withSeminorms ℂ V₁ ℂ).continuous_of_continuous_comp L fun i => ?_
  obtain ⟨p, h, hp, hh, hle⟩ := hb i.1 i.2
  refine Seminorm.continuous_of_le (p := (schwartzSeminormFamily ℂ V₁ ℂ i).comp L) (q := (∫ a, h a ∂μ).toNNReal • p)
    (hp.const_smul _) fun f => ?_
  obtain ⟨T, h1, h2⟩ := norming' _ (cont_seminorm (V := V₁) i.1 i.2) (g f)
  change SchwartzMap.seminorm ℂ i.1 i.2 (g f) ≤ ((∫ a, h a ∂μ).toNNReal : ℝ) * p f
  rw [← h1, (hg f T).2]
  calc ‖∫ a, T (G a f) ∂μ‖ ≤ ∫ a, p f * h a ∂μ :=
        norm_integral_le_of_norm_le (hh.const_mul _) (Eventually.of_forall fun a => (h2 _).trans (hle a f))
    _ = (∫ a, h a ∂μ) * p f := by rw [integral_const_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (apply_nonneg _ _)

end PositivityTheory.ThKG.Loc.Bump

end
