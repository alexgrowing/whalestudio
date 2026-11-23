import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma inner_of_norm_eq (R : H →L[ℂ] H) (hR : ∀ v, ‖R v‖ = ‖v‖) (v w : H) :
    ⟪R v, R w⟫_ℂ = ⟪v, w⟫_ℂ := by
  have h := (LinearMap.norm_map_iff_inner_map_map R).mp hR
  exact h v w

private lemma exists_isometry_extension_of_dense_of_norm_eq {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (V : Submodule ℂ K) (hV : Dense (V : Set K)) (u : V →ₗ[ℂ] K) (hu : ∀ v, ‖u v‖ = ‖v‖) :
    ∃ U : K →L[ℂ] K, (∀ v : V, U v = u v) ∧ ∀ γ, ‖U γ‖ = ‖γ‖ := by
  let uc : V →L[ℂ] K := u.mkContinuous 1 (fun v => by rw [hu, one_mul])
  have hd : DenseRange V.subtypeL := by
    have hr : Set.range (V.subtypeL : V → K) = (V : Set K) := by
      ext x
      simp
    rw [DenseRange, hr]
    exact hV
  have hi : IsUniformInducing V.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  have heq : ∀ v : V, uc.extend V.subtypeL v = u v := fun v => by
    have := ContinuousLinearMap.extend_eq uc hd hi v
    simpa [uc] using this
  refine ⟨uc.extend V.subtypeL, heq, fun γ => ?_⟩
  have hfun := hd.equalizer (g := fun γ => ‖uc.extend V.subtypeL γ‖) (h := fun γ => ‖γ‖)
    (continuous_norm.comp (ContinuousLinearMap.continuous _)) continuous_norm
    (funext fun v => by
      simp only [Function.comp_apply]
      rw [ContinuousLinearMap.extend_eq uc hd hi v]
      simp [uc, hu])
  exact congr_fun hfun γ

lemma abstract {ι K : Type} [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H) (hn : ∀ i v, ‖ρ i v‖ = ‖v‖)
    (hinv : ∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hD : ∀ i, ∀ v ∈ D, ρ i v ∈ D) (J : K →L[ℂ] H) (hJ : Function.Injective J) (s : D → K)
    (hs : DenseRange s) (hJs : ∀ w, J (s w) = w)
    (hsn : ∀ i (w : D), ‖s ⟨ρ i w, hD i w w.2⟩‖ = ‖s w‖) :
    ∃ c : ℝ, ∀ γ : K, ‖J γ‖ ^ 2 = c * ‖γ‖ ^ 2 := by
  classical
  have hadd : ∀ a b : D, s (a + b) = s a + s b := fun a b =>
    hJ (by rw [map_add, hJs, hJs, hJs, Submodule.coe_add])
  have hsmul : ∀ (c : ℂ) (a : D), s (c • a) = c • s a := fun c a =>
    hJ (by rw [map_smul, hJs, hJs, Submodule.coe_smul])
  let sl : D →ₗ[ℂ] K := { toFun := s, map_add' := hadd, map_smul' := hsmul }
  have hinj : Function.Injective sl := fun a b hab => by
    apply Subtype.ext
    rw [← hJs a, ← hJs b]
    exact congrArg J hab
  let e := LinearEquiv.ofInjective sl hinj
  have he : ∀ w : D, e.symm ⟨s w, LinearMap.mem_range_self sl w⟩ = w := fun w => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [e, sl]
  have hVd : Dense ((LinearMap.range sl : Submodule ℂ K) : Set K) := by
    rw [LinearMap.coe_range]
    exact hs
  have hU : ∀ i, ∃ U : K →L[ℂ] K, (∀ w : D, U (s w) = s ⟨ρ i w, hD i w w.2⟩) ∧
      ∀ γ, ‖U γ‖ = ‖γ‖ := by
    intro i
    let r : D →ₗ[ℂ] D := (ρ i).toLinearMap.restrict (fun x hx => hD i x hx)
    let u : LinearMap.range sl →ₗ[ℂ] K := sl ∘ₗ r ∘ₗ e.symm.toLinearMap
    have hu : ∀ w : D, u ⟨s w, LinearMap.mem_range_self sl w⟩ = s ⟨ρ i w, hD i w w.2⟩ :=
      fun w => by
        simp only [u, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
        rfl
    obtain ⟨U, hUeq, hUn⟩ := exists_isometry_extension_of_dense_of_norm_eq _ hVd u (fun v => by
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp v.2
      have hv : v = ⟨s w, LinearMap.mem_range_self sl w⟩ := Subtype.ext hw.symm
      rw [hv, hu, hsn]
      rfl)
    refine ⟨U, fun w => ?_, hUn⟩
    have := hUeq ⟨s w, LinearMap.mem_range_self sl w⟩
    rw [hu] at this
    exact this
  choose U hUs hUn using hU
  have hUinv : ∀ i j, (∀ v, ρ i (ρ j v) = v) → ∀ γ, U i (U j γ) = γ := by
    intro i j hij γ
    have := hs.equalizer (g := fun γ => U i (U j γ)) (h := id)
      ((U i).continuous.comp (U j).continuous) continuous_id (funext fun w => by
        simp only [Function.comp_apply, id]
        rw [hUs j w, hUs i]
        congr 1
        exact Subtype.ext (hij w))
    exact congr_fun this γ
  have hJU : ∀ i γ, J (U i γ) = ρ i (J γ) := by
    intro i γ
    have := hs.equalizer (g := fun γ => J (U i γ)) (h := fun γ => ρ i (J γ))
      (J.continuous.comp (U i).continuous) ((ρ i).continuous.comp J.continuous)
      (funext fun w => by
        simp only [Function.comp_apply]
        rw [hUs i w, hJs, hJs])
    exact congr_fun this γ
  have hadj : ∀ i x, ContinuousLinearMap.adjoint J (ρ i x) = U i (ContinuousLinearMap.adjoint J x) := by
    intro i x
    obtain ⟨j, _, hij⟩ := hinv i
    apply ext_inner_right ℂ
    intro γ
    rw [ContinuousLinearMap.adjoint_inner_left]
    conv_rhs => rw [← hUinv i j hij γ]
    rw [inner_of_norm_eq (U i) (hUn i) (ContinuousLinearMap.adjoint J x) (U j γ),
      ContinuousLinearMap.adjoint_inner_left, hJU j,
      ← inner_of_norm_eq (ρ i) (hn i) x (ρ j (J γ)), hij]
  have hadjρ : ∀ i, ∃ i', ρ i' = ContinuousLinearMap.adjoint (ρ i) := by
    intro i
    obtain ⟨j, _, hij⟩ := hinv i
    refine ⟨j, ?_⟩
    ext v
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_of_norm_eq (ρ i) (hn i) (ρ j v) w, hij]
  let T : H →L[ℂ] H := J ∘L ContinuousLinearMap.adjoint J
  have hcomm : ∀ i, T ∘L ρ i = ρ i ∘L T := by
    intro i
    ext x
    simp only [T, ContinuousLinearMap.comp_apply]
    rw [hadj, hJU]
  obtain ⟨c, hc⟩ := hilbert_schur_of_adjoint_closed ι H ρ hadjρ hirr T hcomm
  have hJJ : ∀ γ, ContinuousLinearMap.adjoint J (J γ) = c • γ := by
    intro γ
    apply hJ
    have := congrArg (fun T' : H →L[ℂ] H => T' (J γ)) hc
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply] at this
    rw [this, map_smul]
  refine ⟨c.re, fun γ => ?_⟩
  have h1 : (⟪γ, γ⟫_ℂ).re = ‖γ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) γ
  have h2 : (⟪γ, γ⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) γ
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (J γ), ← ContinuousLinearMap.adjoint_inner_left J γ (J γ), hJJ,
    inner_smul_left, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im, h1, h2]
  ring

theorem norm_sq_eq : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℝ, ∀ w ∈ D, ‖A w‖ ^ 2 = c * ‖w‖ ^ 2 := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A hA hcl
  classical
  let g : D →ₗ[ℂ] WithLp 2 (H × E) :=
    (WithLp.linearEquiv 2 ℂ (H × E)).symm.toLinearMap ∘ₗ (D.subtype.prod (A ∘ₗ D.subtype))
  have hg : ∀ w : D, g w = WithLp.toLp 2 ((w : H), A w) := fun w => rfl
  let G : Submodule ℂ (WithLp 2 (H × E)) := LinearMap.range g
  let K : Submodule ℂ (WithLp 2 (H × E)) := G.topologicalClosure
  have : CompleteSpace K := G.isClosed_topologicalClosure.completeSpace_coe
  let J : K →L[ℂ] H := (WithLp.fstL 2 ℂ H E) ∘L K.subtypeL
  have hJapp : ∀ γ : K, J γ = (γ : WithLp 2 (H × E)).fst := fun γ => rfl
  let s : D → K := fun w => ⟨g w, G.le_topologicalClosure (LinearMap.mem_range_self g w)⟩
  have hJs : ∀ w, J (s w) = w := fun w => rfl
  have hns : ∀ x : D, ‖s x‖ ^ 2 = ‖(x : H)‖ ^ 2 + ‖A x‖ ^ 2 := fun x =>
    WithLp.prod_norm_sq_eq_of_L2 (g x)
  have hsn : ∀ i (w : D), ‖s ⟨ρ i w, hD i w w.2⟩‖ = ‖s w‖ := by
    intro i w
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hns, hns]
    show ‖ρ i w‖ ^ 2 + ‖A (ρ i w)‖ ^ 2 = _
    rw [hn, hA i w w.2]
  have hs : DenseRange s := by
    rw [Metric.denseRange_iff]
    intro γ ε hε
    have hmem : (γ : WithLp 2 (H × E)) ∈ closure (G : Set (WithLp 2 (H × E))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact γ.2
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hmem ε hε
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hb
    exact ⟨w, hd⟩
  have hJ : Function.Injective J := by
    rw [injective_iff_map_eq_zero]
    intro γ hγ
    have hmem : (γ : WithLp 2 (H × E)) ∈ closure (G : Set (WithLp 2 (H × E))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact γ.2
    obtain ⟨x, hxG, hx⟩ := mem_closure_iff_seq_limit.mp hmem
    choose w hw using fun n => LinearMap.mem_range.mp (hxG n)
    have h1 : Tendsto (fun n => ((w n : D) : H)) atTop (𝓝 0) := by
      have := ((WithLp.fstL 2 ℂ H E).continuous.tendsto _).comp hx
      have h0 : (WithLp.fstL 2 ℂ H E) (γ : WithLp 2 (H × E)) = 0 := hγ
      rw [h0] at this
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, ← hw n, hg]
      rfl
    have h2 : Tendsto (fun n => A ((w n : D) : H)) atTop (𝓝 (γ : WithLp 2 (H × E)).snd) := by
      have := ((WithLp.sndL 2 ℂ H E).continuous.tendsto _).comp hx
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, ← hw n, hg]
      rfl
    have h3 := hcl (fun n => ((w n : D) : H)) _ (fun n => (w n).2) h1 h2
    have h4 : (γ : WithLp 2 (H × E)).fst = 0 := hγ
    apply Subtype.ext
    have h5 : ‖(γ : WithLp 2 (H × E))‖ ^ 2 = 0 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, h3, h4]
      simp
    simpa using h5
  obtain ⟨c, hc⟩ := abstract (H := H) ρ D hn hinv hirr hD J hJ s hs hJs hsn
  refine ⟨(1 - c) / c, fun w hw => ?_⟩
  have h : ‖w‖ ^ 2 = c * (‖w‖ ^ 2 + ‖A w‖ ^ 2) := by
    have := hc (s ⟨w, hw⟩)
    rw [hJs, hns] at this
    exact this
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul] at h
    have hw0 : w = 0 := by simpa using h
    subst hw0
    simp
  · rw [div_mul_eq_mul_div, eq_div_iff hc0]
    linear_combination (-1 : ℝ) * h

end GlobalTheory.ClosableSchur
