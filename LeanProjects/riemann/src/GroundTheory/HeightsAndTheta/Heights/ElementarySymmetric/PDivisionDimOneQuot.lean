import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionDimOneQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace DivisionDimOneQuot

theorem local_quot {f σ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hf : AnalyticAt ℂ f z₀)
    (hσ : AnalyticAt ℂ σ z₀) (hσ0 : σ z₀ = 0) (hσ' : deriv σ z₀ ≠ 0)
    (hfm : ∀ k < m, iteratedDeriv k f z₀ = 0) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q z₀ ∧ (∀ᶠ z in 𝓝 z₀, f z = σ z ^ m * Q z) ∧
      ∀ᶠ z in 𝓝[≠] z₀, σ z ≠ 0 := by
  obtain ⟨u, hu, hu0, hσu⟩ := (hσ.analyticOrderAt_eq_natCast (n := 1)).1
    (by simpa using hσ.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hσ0 hσ')
  obtain ⟨f₁, hf₁, hff₁⟩ := (natCast_le_analyticOrderAt (n := m) hf).1
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).2 hfm)
  have hune : ∀ᶠ z in 𝓝 z₀, u z ≠ 0 := hu.continuousAt.eventually_ne hu0
  refine ⟨fun z => f₁ z / u z ^ m, hf₁.div (hu.pow m) (pow_ne_zero _ hu0), ?_, ?_⟩
  · filter_upwards [hσu, hff₁, hune] with z h1 h2 h3
    rw [h2, h1, smul_eq_mul, smul_eq_mul, pow_one, mul_pow]
    field_simp
  · filter_upwards [nhdsWithin_le_nhds hσu, nhdsWithin_le_nhds hune, self_mem_nhdsWithin]
      with z h1 h3 h4
    rw [h1, smul_eq_mul, pow_one]
    exact mul_ne_zero (sub_ne_zero.2 h4) h3

abbrev coordFin1 : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ

theorem det_fin_one (L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ)) :
    LinearMap.det (L : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) = L (fun _ => 1) 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique,
    LinearMap.toMatrix_apply]
  have : (Pi.single 0 1 : Fin 1 → ℂ) = fun _ => 1 := by
    funext i
    fin_cases i
    simp
  simp [this]

variable {U : Type} [TopologicalSpace U]

theorem punctured_neBot (A : FinHolAtlas 1 U) (x : U) : (𝓝[≠] x).NeBot := by
  rw [neBot_iff]
  intro h
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have ho : IsOpen ({x} : Set U) := (isOpen_singleton_iff_punctured_nhds x).2 h
  have := (A.chart (chartIdx A x)).isOpen_image_of_subset_source ho
    (Set.singleton_subset_iff.2 hx)
  rw [Set.image_singleton] at this
  exact not_isOpen_singleton _ this

theorem continuousAt_of_chart (A : FinHolAtlas 1 U) {f : U → ℂ} {c : Fin A.n} {x : U}
    (hx : x ∈ (A.chart c).source) (h : ContinuousAt (f ∘ (A.chart c).symm) (A.chart c x)) :
    ContinuousAt f x := by
  have h2 : ContinuousAt ((f ∘ (A.chart c).symm) ∘ A.chart c) x :=
    h.comp ((A.chart c).continuousAt hx)
  refine h2.congr ?_
  filter_upwards [(A.chart c).eventually_left_inverse hx] with y hy
  simp [hy]

theorem jac_comp_analyticAt (A : FinHolAtlas 1 U) (j k i : Fin A.n) {y : Fin 1 → ℂ}
    (hy : y ∈ (A.chart i).target) (hj : (A.chart i).symm y ∈ (A.chart j).source)
    (hk : (A.chart i).symm y ∈ (A.chart k).source) :
    AnalyticAt ℂ (fun y => jac A j k ((A.chart i).symm y)) y := by
  have hτ : AnalyticAt ℂ (A.chart j ∘ (A.chart i).symm) y := A.holo i j y ⟨hy, hj⟩
  have hmem : (A.chart j ∘ (A.chart i).symm) y ∈
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, Function.comp_apply, (A.chart j).left_inv hj]
    exact hk
  have hd : AnalyticAt ℂ (fderiv ℂ (A.chart k ∘ (A.chart j).symm))
      ((A.chart j ∘ (A.chart i).symm) y) := (A.holo j k _ hmem).fderiv
  have hev : AnalyticAt ℂ (fun L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ) => L (fun _ => 1) 0)
      (fderiv ℂ (A.chart k ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) y)) :=
    (((ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℂ] ℂ)).comp
      (ContinuousLinearMap.apply ℂ (Fin 1 → ℂ) (fun _ : Fin 1 => (1 : ℂ)) :
        ((Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ)) →L[ℂ] (Fin 1 → ℂ))).analyticAt _
  have := hev.comp_of_eq (hd.comp hτ) rfl
  refine this.congr (Filter.Eventually.of_forall fun y' => ?_)
  simp [jac, det_fin_one]

variable {X : EmbDatum 1} (Z : ZeroDatum X)

theorem s_mem : Z.s 0 ∈ X.L.sections 1 := by
  show lin X.e (Z.c 0) ∈ _
  unfold lin
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)

theorem mem_zeroSet_of {j : Fin X.A.n} {x : X.U} (hxj : x ∈ (X.A.chart j).source)
    (h : Z.s 0 j x = 0) : x ∈ zeroSet X.A Z.s := by
  have hxc : x ∈ (X.A.chart (chartIdx X.A x)).source := Classical.choose_spec (X.A.cover x)
  show ∀ i, Z.s i (chartIdx X.A x) x = 0
  intro i
  rw [Subsingleton.elim i 0]
  have h1 := (s_mem Z).2.1 j (chartIdx X.A x) x ⟨hxj, hxc⟩
  rw [h, pow_one] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left (X.L.ne_zero _ _ x ⟨hxj, hxc⟩)

open scoped Classical in

def quot (X : EmbDatum 1) (s F : Fin X.A.n → X.U → ℂ) (m : ℕ) (j : Fin X.A.n) (x : X.U) : ℂ :=
  if x ∈ (X.A.chart j).source ∧ s j x = 0 then
    limUnder (𝓝[≠] x) (fun y => F j y / s j y ^ m)
  else F j x / s j x ^ m

def locQ (X : EmbDatum 1) (Q : ℂ → ℂ) (j c : Fin X.A.n) (x : X.U) : ℂ :=
  jac X.A j c x * X.L₂.g j c x * X.L.g j c x ^ (1 + 1) * Q (coordFin1 (X.A.chart c x))

theorem quot_alg {a b g sk Fk : ℂ} (m : ℕ) (hg : g ≠ 0) (hsk : sk ≠ 0) :
    a * b * g ^ (1 + (m + 1)) * Fk / (g ^ 1 * sk) ^ m = a * b * g ^ (1 + 1) * (Fk / sk ^ m) := by
  field_simp
  ring

theorem chart_data {m : ℕ} {F : Fin X.A.n → X.U → ℂ}
    (hF : F ∈ topSections X.A X.L₂ X.L (1 + (m + 1))) (hfil : IsFil X.A Z.s F m)
    {x₀ : X.U} (hx₀ : x₀ ∈ zeroSet X.A Z.s) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q (coordFin1 (X.A.chart (chartIdx X.A x₀) x₀)) ∧
      (∀ᶠ x in 𝓝 x₀, F (chartIdx X.A x₀) x =
        Z.s 0 (chartIdx X.A x₀) x ^ m * Q (coordFin1 (X.A.chart (chartIdx X.A x₀) x))) ∧
      ∀ᶠ x in 𝓝[≠] x₀, Z.s 0 (chartIdx X.A x₀) x ≠ 0 := by
  have hx₀c : x₀ ∈ (X.A.chart (chartIdx X.A x₀)).source := Classical.choose_spec (X.A.cover x₀)
  have hfil' := hfil x₀ hx₀
  have hnd : sJac X.A Z.s (chartIdx X.A x₀) x₀ ≠ 0 := Z.nondeg x₀ hx₀
  have hz : Z.s 0 (chartIdx X.A x₀) x₀ = 0 := hx₀ 0
  generalize chartIdx X.A x₀ = c at hx₀c hfil' hnd hz ⊢
  set φ := X.A.chart c with hφ
  have hy₀ : φ x₀ ∈ φ.target := φ.map_source hx₀c
  have hl : φ.symm (φ x₀) = x₀ := φ.left_inv hx₀c
  have hs := s_mem Z
  have hFa : AnalyticAt ℂ (F c ∘ φ.symm) (φ x₀) :=
    hF.1 c c (φ x₀) ⟨hy₀, by show φ.symm (φ x₀) ∈ φ.source; rw [hl]; exact hx₀c⟩
  have hsa : AnalyticAt ℂ (Z.s 0 c ∘ φ.symm) (φ x₀) :=
    hs.1 c c (φ x₀) ⟨hy₀, by show φ.symm (φ x₀) ∈ φ.source; rw [hl]; exact hx₀c⟩
  set z₀ := coordFin1 (φ x₀) with hz₀def
  have hz₀ : coordFin1.symm z₀ = φ x₀ := coordFin1.symm_apply_apply _
  have hsymm : AnalyticAt ℂ (fun w : ℂ => coordFin1.symm w) z₀ :=
    (coordFin1.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt z₀
  have hfa : AnalyticAt ℂ (fun w => F c (φ.symm (coordFin1.symm w))) z₀ :=
    hFa.comp_of_eq hsymm hz₀
  have hσa : AnalyticAt ℂ (fun w => Z.s 0 c (φ.symm (coordFin1.symm w))) z₀ :=
    hsa.comp_of_eq hsymm hz₀
  have hσ0 : (fun w => Z.s 0 c (φ.symm (coordFin1.symm w))) z₀ = 0 := by
    show Z.s 0 c (φ.symm (coordFin1.symm z₀)) = 0
    rw [hz₀, hl]
    exact hz

  let G : (Fin 1 → ℂ) → (Fin 1 → ℂ) := fun z i => Z.s i c (φ.symm z)
  have hGa : AnalyticAt ℂ G (φ x₀) := by
    rw [analyticAt_pi_iff]
    intro i
    rw [Subsingleton.elim i 0]
    exact hsa
  have hGd : HasFDerivAt G (fderiv ℂ G (φ x₀)) (coordFin1.symm z₀) := by
    rw [hz₀]; exact hGa.differentiableAt.hasFDerivAt
  have h2 := ((ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℂ] ℂ).hasFDerivAt).comp z₀
    (hGd.comp z₀ (coordFin1.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).hasFDerivAt)
  have hσd : HasDerivAt (fun w => Z.s 0 c (φ.symm (coordFin1.symm w)))
      (fderiv ℂ G (φ x₀) (fun _ => 1) 0) z₀ := by
    have h3 : HasDerivAt (fun w => Z.s 0 c (φ.symm (coordFin1.symm w)))
        ((ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℂ] ℂ).comp
          ((fderiv ℂ G (φ x₀)).comp (coordFin1.symm : ℂ →L[ℂ] (Fin 1 → ℂ))) 1) z₀ :=
      h2.hasDerivAt
    refine h3.congr_deriv ?_
    simp
    rfl
  have hσ' : deriv (fun w => Z.s 0 c (φ.symm (coordFin1.symm w))) z₀ ≠ 0 := by
    rw [hσd.deriv]
    have : sJac X.A Z.s c x₀ = fderiv ℂ G (φ x₀) (fun _ => 1) 0 := by
      rw [sJac, det_fin_one]
      rfl
    rw [← this]
    exact hnd
  have hvan : ∀ k < m, iteratedDeriv k (fun w => F c (φ.symm (coordFin1.symm w))) z₀ = 0 := by
    intro k hk
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have h1 := coordFin1.symm.iteratedFDerivWithin_comp_right (F c ∘ φ.symm) uniqueDiffOn_univ
      (Set.mem_univ (coordFin1.symm z₀)) k
    rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h1
    have h4 : (fun w => F c (φ.symm (coordFin1.symm w))) = (F c ∘ φ.symm) ∘ coordFin1.symm := rfl
    rw [h4, h1, hz₀, hfil' k hk]
    simp
  obtain ⟨Q, hQ, hfeq, hσne⟩ := local_quot hfa hσa hσ0 hσ' hvan
  have hψ : Tendsto (fun x => coordFin1 (φ x)) (𝓝 x₀) (𝓝 z₀) :=
    (coordFin1.continuous.continuousAt.comp (φ.continuousAt hx₀c)).tendsto
  refine ⟨Q, hQ, ?_, ?_⟩
  · filter_upwards [hψ.eventually hfeq, φ.open_source.mem_nhds hx₀c] with x h1 h2
    have h5 : φ.symm (coordFin1.symm (coordFin1 (φ x))) = x := by
      rw [coordFin1.symm_apply_apply, φ.left_inv h2]
    simp only [h5] at h1
    exact h1
  · have hψ' : Tendsto (fun x => coordFin1 (φ x)) (𝓝[≠] x₀) (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hψ.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (φ.open_source.mem_nhds hx₀c), self_mem_nhdsWithin]
        with x h2 h3
      intro h4
      exact h3 (φ.injOn h2 hx₀c (coordFin1.injective h4))
    filter_upwards [hψ'.eventually hσne, nhdsWithin_le_nhds (φ.open_source.mem_nhds hx₀c)]
      with x h1 h2
    have h5 : φ.symm (coordFin1.symm (coordFin1 (φ x))) = x := by
      rw [coordFin1.symm_apply_apply, φ.left_inv h2]
    simp only [h5] at h1
    exact h1

theorem locQ_analyticAt (Q : ℂ → ℂ) (j c i : Fin X.A.n) {y : Fin 1 → ℂ}
    (hy : y ∈ (X.A.chart i).target) (hj : (X.A.chart i).symm y ∈ (X.A.chart j).source)
    (hc : (X.A.chart i).symm y ∈ (X.A.chart c).source)
    (hQ : AnalyticAt ℂ Q (coordFin1 (X.A.chart c ((X.A.chart i).symm y)))) :
    AnalyticAt ℂ (locQ X Q j c ∘ (X.A.chart i).symm) y := by
  have h1 := jac_comp_analyticAt X.A j c i hy hj hc
  have h2 : AnalyticAt ℂ (X.L₂.g j c ∘ (X.A.chart i).symm) y := X.L₂.holo j c i y ⟨hy, hj, hc⟩
  have h3 : AnalyticAt ℂ (X.L.g j c ∘ (X.A.chart i).symm) y := X.L.holo j c i y ⟨hy, hj, hc⟩
  have h4 : AnalyticAt ℂ (X.A.chart c ∘ (X.A.chart i).symm) y := X.A.holo i c y ⟨hy, hc⟩
  have h5 : AnalyticAt ℂ (fun y => Q (coordFin1 (X.A.chart c ((X.A.chart i).symm y)))) y :=
    hQ.comp_of_eq (((coordFin1 : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt _).comp h4) rfl
  exact ((h1.mul h2).mul (h3.pow _)).mul h5

theorem locQ_continuousAt (Q : ℂ → ℂ) (j c : Fin X.A.n) {x : X.U}
    (hxj : x ∈ (X.A.chart j).source) (hxc : x ∈ (X.A.chart c).source)
    (hQ : AnalyticAt ℂ Q (coordFin1 (X.A.chart c x))) : ContinuousAt (locQ X Q j c) x := by
  have hl := (X.A.chart c).left_inv hxc
  have := locQ_analyticAt Q j c c ((X.A.chart c).map_source hxc) (by rw [hl]; exact hxj)
    (by rw [hl]; exact hxc) (by rw [hl]; exact hQ)
  exact continuousAt_of_chart X.A hxc this.continuousAt

theorem quot_eventuallyEq {m : ℕ} {F : Fin X.A.n → X.U → ℂ}
    (hF : F ∈ topSections X.A X.L₂ X.L (1 + (m + 1))) {j : Fin X.A.n} {x₀ : X.U}
    (hx₀j : x₀ ∈ (X.A.chart j).source) {Q : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q (coordFin1 (X.A.chart (chartIdx X.A x₀) x₀)))
    (hFQ : ∀ᶠ x in 𝓝 x₀, F (chartIdx X.A x₀) x =
        Z.s 0 (chartIdx X.A x₀) x ^ m * Q (coordFin1 (X.A.chart (chartIdx X.A x₀) x)))
    (hne : ∀ᶠ x in 𝓝[≠] x₀, Z.s 0 (chartIdx X.A x₀) x ≠ 0) (hs0 : Z.s 0 j x₀ = 0) :
    quot X (Z.s 0) F m j =ᶠ[𝓝 x₀] locQ X Q j (chartIdx X.A x₀) := by
  have hx₀c : x₀ ∈ (X.A.chart (chartIdx X.A x₀)).source := Classical.choose_spec (X.A.cover x₀)
  generalize chartIdx X.A x₀ = c at hx₀c hQ hFQ hne ⊢
  have hs := s_mem Z
  have hW : ∀ᶠ x in 𝓝 x₀, x ∈ (X.A.chart j).source ∩ (X.A.chart c).source :=
    ((X.A.chart j).open_source.inter (X.A.chart c).open_source).mem_nhds ⟨hx₀j, hx₀c⟩
  have hpunct : ∀ᶠ x in 𝓝[≠] x₀, Z.s 0 j x ≠ 0 ∧
      F j x / Z.s 0 j x ^ m = locQ X Q j c x := by
    filter_upwards [nhdsWithin_le_nhds hW, nhdsWithin_le_nhds hFQ, hne] with x hx h1 h2
    have hg := X.L.ne_zero j c x hx
    have hsj : Z.s 0 j x = X.L.g j c x ^ 1 * Z.s 0 c x := hs.2.1 j c x hx
    have hFj := hF.2.1 j c x hx
    refine ⟨by rw [hsj]; exact mul_ne_zero (pow_ne_zero _ hg) h2, ?_⟩
    rw [hFj, hsj, quot_alg m hg h2, h1, locQ]
    field_simp
  have hcont := locQ_continuousAt Q j c hx₀j hx₀c hQ
  have := punctured_neBot X.A x₀
  have hlim : limUnder (𝓝[≠] x₀) (fun y => F j y / Z.s 0 j y ^ m) = locQ X Q j c x₀ :=
    (Filter.Tendsto.congr' (hpunct.mono fun x hx => hx.2.symm)
      (hcont.tendsto.mono_left nhdsWithin_le_nhds)).limUnder_eq
  show ∀ᶠ x in 𝓝 x₀, quot X (Z.s 0) F m j x = locQ X Q j c x
  rw [← nhdsNE_sup_pure, eventually_sup, eventually_pure]
  refine ⟨hpunct.mono fun x hx => ?_, ?_⟩
  · simp only [quot, hx.1, and_false, if_false]
    exact hx.2
  · simp only [quot, hx₀j, hs0, and_self, if_true]
    exact hlim

theorem quot_holoOn {m : ℕ} {F : Fin X.A.n → X.U → ℂ}
    (hF : F ∈ topSections X.A X.L₂ X.L (1 + (m + 1))) (hfil : IsFil X.A Z.s F m)
    (j : Fin X.A.n) : X.A.HoloOn (X.A.chart j).source (quot X (Z.s 0) F m j) := by
  intro i y hy'
  obtain ⟨hy, hyj⟩ := hy'
  have hs := s_mem Z
  have hyj' : (X.A.chart i).symm y ∈ (X.A.chart j).source := hyj
  by_cases hs0 : Z.s 0 j ((X.A.chart i).symm y) = 0
  · have hz := mem_zeroSet_of Z hyj' hs0
    obtain ⟨Q, hQ, hFQ, hne⟩ := chart_data Z hF hfil hz
    have heq := quot_eventuallyEq Z hF hyj' hQ hFQ hne hs0
    have hx₀c : (X.A.chart i).symm y ∈ (X.A.chart (chartIdx X.A ((X.A.chart i).symm y))).source :=
      Classical.choose_spec (X.A.cover _)
    have han := locQ_analyticAt Q j (chartIdx X.A ((X.A.chart i).symm y)) i hy hyj' hx₀c hQ
    exact han.congr ((((X.A.chart i).continuousAt_symm hy).eventually heq).mono
      fun _ h => h.symm)
  · have hFa : AnalyticAt ℂ (F j ∘ (X.A.chart i).symm) y := hF.1 j i y ⟨hy, hyj⟩
    have hsa : AnalyticAt ℂ (Z.s 0 j ∘ (X.A.chart i).symm) y := hs.1 j i y ⟨hy, hyj⟩
    have hev : ∀ᶠ y' in 𝓝 y, Z.s 0 j ((X.A.chart i).symm y') ≠ 0 :=
      hsa.continuousAt.eventually_ne hs0
    refine (hFa.div (hsa.pow m) (pow_ne_zero _ hs0)).congr (hev.mono fun y' hy' => ?_)
    show F j ((X.A.chart i).symm y') / Z.s 0 j ((X.A.chart i).symm y') ^ m =
      quot X (Z.s 0) F m j ((X.A.chart i).symm y')
    simp only [quot, hy', and_false, if_false]

theorem quot_continuousAt {m : ℕ} {F : Fin X.A.n → X.U → ℂ}
    (hF : F ∈ topSections X.A X.L₂ X.L (1 + (m + 1))) (hfil : IsFil X.A Z.s F m)
    {j : Fin X.A.n} {x : X.U} (hxj : x ∈ (X.A.chart j).source) (hs0 : Z.s 0 j x = 0) :
    ContinuousAt (quot X (Z.s 0) F m j) x := by
  have hz := mem_zeroSet_of Z hxj hs0
  obtain ⟨Q, hQ, hFQ, hne⟩ := chart_data Z hF hfil hz
  have heq := quot_eventuallyEq Z hF hxj hQ hFQ hne hs0
  have hxc : x ∈ (X.A.chart (chartIdx X.A x)).source := Classical.choose_spec (X.A.cover x)
  exact (locQ_continuousAt Q j _ hxj hxc hQ).congr heq.symm

theorem continuousAt_of_holoOn {W : Set X.U} {f : X.U → ℂ} (hf : X.A.HoloOn W f) {j : Fin X.A.n}
    {x : X.U} (hxj : x ∈ (X.A.chart j).source) (hxW : x ∈ W) : ContinuousAt f x := by
  have hl := (X.A.chart j).left_inv hxj
  refine continuousAt_of_chart X.A hxj (hf j _ ⟨(X.A.chart j).map_source hxj, ?_⟩).continuousAt
  show (X.A.chart j).symm (X.A.chart j x) ∈ W
  rw [hl]
  exact hxW

theorem quot_compat {m : ℕ} {F : Fin X.A.n → X.U → ℂ}
    (hF : F ∈ topSections X.A X.L₂ X.L (1 + (m + 1))) (hfil : IsFil X.A Z.s F m)
    (j k : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart k).source) :
    quot X (Z.s 0) F m j x =
      jac X.A j k x * X.L₂.g j k x * X.L.g j k x ^ (1 + 1) * quot X (Z.s 0) F m k x := by
  have hs := s_mem Z
  have hoff : ∀ y ∈ (X.A.chart j).source ∩ (X.A.chart k).source, Z.s 0 k y ≠ 0 →
      quot X (Z.s 0) F m j y =
        jac X.A j k y * X.L₂.g j k y * X.L.g j k y ^ (1 + 1) * quot X (Z.s 0) F m k y := by
    intro y hy hsk
    have hg := X.L.ne_zero j k y hy
    have hsj : Z.s 0 j y = X.L.g j k y ^ 1 * Z.s 0 k y := hs.2.1 j k y hy
    have hsj0 : Z.s 0 j y ≠ 0 := by rw [hsj]; exact mul_ne_zero (pow_ne_zero _ hg) hsk
    simp only [quot, hsj0, hsk, and_false, if_false]
    rw [hF.2.1 j k y hy, hsj]
    exact quot_alg m hg hsk
  by_cases hsk : Z.s 0 k x = 0
  · have hz := mem_zeroSet_of Z hx.2 hsk
    have hsj : Z.s 0 j x = 0 := by rw [hs.2.1 j k x hx, hsk, mul_zero]
    obtain ⟨Q, hQ, hFQ, hne⟩ := chart_data Z hF hfil hz
    have hxc : x ∈ (X.A.chart (chartIdx X.A x)).source := Classical.choose_spec (X.A.cover x)
    have hcj := quot_continuousAt Z hF hfil hx.1 hsj
    have hck := quot_continuousAt Z hF hfil hx.2 hsk
    have hjac : ContinuousAt (jac X.A j k) x := by
      have hl := (X.A.chart j).left_inv hx.1
      refine continuousAt_of_chart X.A hx.1 (jac_comp_analyticAt X.A j k j
        ((X.A.chart j).map_source hx.1) ?_ ?_).continuousAt
      · rw [hl]; exact hx.1
      · rw [hl]; exact hx.2
    have hg₂ := continuousAt_of_holoOn (X.L₂.holo j k) hx.1 hx
    have hg := continuousAt_of_holoOn (X.L.holo j k) hx.1 hx
    have hR := ((hjac.mul hg₂).mul (hg.pow (1 + 1))).mul hck
    have := punctured_neBot X.A x
    have hW : ∀ᶠ y in 𝓝 x, y ∈ ((X.A.chart j).source ∩ (X.A.chart k).source) ∩
        (X.A.chart (chartIdx X.A x)).source :=
      (((X.A.chart j).open_source.inter (X.A.chart k).open_source).inter
        (X.A.chart (chartIdx X.A x)).open_source).mem_nhds ⟨hx, hxc⟩
    have hev : quot X (Z.s 0) F m j =ᶠ[𝓝[≠] x]
        fun y => jac X.A j k y * X.L₂.g j k y * X.L.g j k y ^ (1 + 1) *
          quot X (Z.s 0) F m k y := by
      filter_upwards [nhdsWithin_le_nhds hW, hne] with y hy hsc
      refine hoff y hy.1 ?_
      have h1 := hs.2.1 k (chartIdx X.A x) y ⟨hy.1.2, hy.2⟩
      rw [h1]
      exact mul_ne_zero (pow_ne_zero _ (X.L.ne_zero _ _ y ⟨hy.1.2, hy.2⟩)) hsc
    exact tendsto_nhds_unique ((hcj.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
      (hR.tendsto.mono_left nhdsWithin_le_nhds)
  · exact hoff x hx hsk

theorem quot_mul {m : ℕ} {F : Fin X.A.n → X.U → ℂ}
    (hF : F ∈ topSections X.A X.L₂ X.L (1 + (m + 1))) (hfil : IsFil X.A Z.s F m)
    (j : Fin X.A.n) (x : X.U) : F j x = Z.s 0 j x ^ m * quot X (Z.s 0) F m j x := by
  by_cases h : x ∈ (X.A.chart j).source ∧ Z.s 0 j x = 0
  · obtain ⟨hxj, hs0⟩ := h
    have hz := mem_zeroSet_of Z hxj hs0
    obtain ⟨Q, hQ, hFQ, hne⟩ := chart_data Z hF hfil hz
    have heq := (quot_eventuallyEq Z hF hxj hQ hFQ hne hs0).self_of_nhds
    have hxc : x ∈ (X.A.chart (chartIdx X.A x)).source := Classical.choose_spec (X.A.cover x)
    have hsc : Z.s 0 (chartIdx X.A x) x = 0 := hz 0
    rw [heq, hF.2.1 j _ x ⟨hxj, hxc⟩, hFQ.self_of_nhds, hsc, hs0, locQ]
    by_cases hm : m = 0
    · subst hm
      simp only [pow_zero, one_mul]
    · simp [zero_pow hm]
  · simp only [quot, h, if_false]
    by_cases hs : Z.s 0 j x = 0
    · have hxj : x ∉ (X.A.chart j).source := fun hx => h ⟨hx, hs⟩
      rw [hF.2.2 j x hxj]
      simp
    · field_simp

end DivisionDimOneQuot

open DivisionDimOneQuot in

theorem DivisionDimOneQuot.proof : DivisionDimOneQuot.Statement := by
  intro T X Z hT F hF hfil
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hfil ⊢
  refine ⟨quot X (Z.s 0) F m, ⟨fun j => quot_holoOn Z hF hfil j,
    fun j k x hx => quot_compat Z hF hfil j k x hx, fun j x hx => ?_⟩, ?_⟩
  · simp [quot, hx, hF.2.2 j x hx]
  · funext j x
    simp only [Pi.mul_apply, Pi.pow_apply]
    exact quot_mul Z hF hfil j x

end

end GroundTheory.Heights₂.Heights.EffectiveHS
