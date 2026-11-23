import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section Helpers

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

def flO (w0 : ι → Y → ℂ) (i : ι) : Set (V n) :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' {y | w0 i y ≠ 0}

theorem denominator_ne_zero_on_chart (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : w0 i x ≠ 0 := by

  have hw := hD.isSection_denom
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw
  rw [hw.2 i (A.pick x) x trivial hi (A.mem_pick x)]
  exact mul_ne_zero (A.g_ne L i (A.pick x) x hi (A.mem_pick x)) hx.1

theorem denominator_ne_zero_of_overlap (hD : A.D0 L w w0 s) {y : Y} {i j : ι} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) : w0 i y ≠ 0 := by

  have hw := hD.isSection_denom
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw
  rw [hw.2 i j y trivial hi hj]
  exact mul_ne_zero (A.g_ne L i j y hi hj) h

theorem flL_zLoc_chart (hD : A.D0 L w w0 s) {y : Y} {i : ι} (hi : y ∈ (A.chart i).source)
    (_hne : w0 i y ≠ 0) : A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by

  have hp := A.mem_pick y
  unfold WeightedAtlas.zLoc WeightedAtlas.zmap
  rw [(A.chart i).left_inv hi]
  congr 1
  funext k
  have hw := hD.isSection_denom
  have hs := hD.sec_s k
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw hs
  rw [hw.2 i (A.pick y) y trivial hi hp, hs.2 i (A.pick y) y trivial hi hp]
  exact mul_div_mul_left _ _ (A.g_ne L i (A.pick y) y hi hp)

theorem flL_isOpen_O (hD : A.D0 L w w0 s) (i : ι) : IsOpen (flO A w0 i) := by

  have hw := hD.isSection_denom
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw
  have hc : ContinuousOn (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hw.1 i).continuousOn
    simpa using this
  unfold flO
  exact hc.isOpen_inter_preimage (A.chart i).open_target (isOpen_ne (x := (0 : ℂ)))

theorem flL_comp_diff (hD : A.D0 L w w0 s) (i : ι) (k : Fin n) :
    DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v))
      (flO A w0 i) := by

  have hw := hD.isSection_denom
  have hs := hD.sec_s k
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw hs
  have h1 : DifferentiableOn ℂ (s k i ∘ (A.chart i).symm) (flO A w0 i) :=
    (hs.1 i).mono (fun v hv => ⟨hv.1, Set.mem_univ _⟩)
  have h2 : DifferentiableOn ℂ (w0 i ∘ (A.chart i).symm) (flO A w0 i) :=
    (hw.1 i).mono (fun v hv => ⟨hv.1, Set.mem_univ _⟩)
  have h3 : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) * (w0 i ((A.chart i).symm v))⁻¹)
      (flO A w0 i) := DifferentiableOn.mul h1 (DifferentiableOn.inv h2 (fun v (hv : v ∈ flO A w0 i) => hv.2))
  simpa only [div_eq_mul_inv] using h3

theorem flL_zLoc_contDiffOn (hD : A.D0 L w w0 s) (i : ι) :
    ContDiffOn ℂ ∞ (A.zLoc w0 s i) (flO A w0 i) := by

  unfold WeightedAtlas.zLoc
  rw [contDiffOn_piLp]
  intro k
  simp only [WithLp.ofLp_toLp]
  exact ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn_complex (flL_isOpen_O A hD i) (flL_comp_diff A hD i k)

theorem flL_mem_O (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : A.chart i x ∈ flO A w0 i := by
  refine ⟨(A.chart i).map_source hi, ?_⟩
  show w0 i ((A.chart i).symm (A.chart i x)) ≠ 0
  rw [(A.chart i).left_inv hi]
  exact denominator_ne_zero_on_chart A hD hx hi

theorem flL_zLoc_contDiffAt (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : ContDiffAt ℂ ∞ (A.zLoc w0 s i) (A.chart i x) := (flL_zLoc_contDiffOn A hD i).contDiffAt ((flL_isOpen_O A hD i).mem_nhds (flL_mem_O A hD hx hi))

theorem flL_jz_trans (hD : A.D0 L w w0 s) {y : Y} (hy : y ∈ A.Mset w0 s De) {i j : ι}
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    jz A w0 s j y = (jz A w0 s i y).comp
      (fderiv ℂ (A.chart i ∘ (A.chart j).symm) (A.chart j y)) := by

  unfold jz
  have hp : A.chart i ((A.chart j).symm (A.chart j y)) = A.chart i y := by
    rw [(A.chart j).left_inv hj]
  have hO : IsOpen (ovl A.chart j i) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (A.chart i).open_source
  have hm : A.chart j y ∈ ovl A.chart j i := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j y) ∈ (A.chart i).source
    rw [(A.chart j).left_inv hj]
    exact hi
  have hT : DifferentiableAt ℂ (A.chart i ∘ (A.chart j).symm) (A.chart j y) :=
    (A.holo_trans j i).differentiableAt (hO.mem_nhds hm)
  have hZ : DifferentiableAt ℂ (A.zLoc w0 s i) ((A.chart i ∘ (A.chart j).symm) (A.chart j y)) := by
    rw [Function.comp_apply, hp]
    exact (flL_zLoc_contDiffAt A hD hy hi).differentiableAt (by simp)
  have hE : A.zLoc w0 s j =ᶠ[𝓝 (A.chart j y)] A.zLoc w0 s i ∘ (A.chart i ∘ (A.chart j).symm) := by
    filter_upwards [hO.mem_nhds hm] with v hv
    have hpj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hpi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    simp only [WeightedAtlas.zLoc, Function.comp_apply, (A.chart i).left_inv hpi]
    congr 1
    funext k
    have hw := hD.isSection_denom
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw hs
    rw [hw.2 j i _ trivial hpj hpi, hs.2 j i _ trivial hpj hpi]
    exact mul_div_mul_left _ _ (A.g_ne L j i _ hpj hpi)
  rw [hE.fderiv_eq, fderiv_comp _ hZ hT, Function.comp_apply, hp]

theorem flL_det_trans (hD : A.D0 L w w0 s) {y : Y} (hy : y ∈ A.Mset w0 s De) {i j : ι}
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    (jz A w0 s i y).det = (jz A w0 s j y).det * A.g A.kap i j y := by

  rw [flL_jz_trans A hD hy hj hi, A.g_kap i j y hi hj]
  simp only [ContinuousLinearMap.det]
  exact LinearMap.det_comp _ _

end Helpers

section Det

variable {n : ℕ}

theorem flL_det_eq (f : V n →L[ℂ] V n) :
    f.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ c, f (bas n c) (σ c) := by

  simp only [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [LinearMap.toMatrix_apply, bas, Units.smul_def, zsmul_eq_mul]

theorem flL_det_contDiffAt {G : V n → V n →L[ℂ] V n} {y : V n} (hG : ContDiffAt ℂ ∞ G y) :
    ContDiffAt ℂ ∞ (fun v => (G v).det) y := by

  have e : (fun v => (G v).det) = fun v => ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℂ) * ∏ c, G v (bas n c) (σ c) := funext fun v => flL_det_eq (G v)
  rw [e]
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => ?_)
  exact ((EuclideanSpace.proj (σ c)).comp
    (ContinuousLinearMap.apply ℂ (V n) (bas n c))).contDiff.contDiffAt.comp y hG

end Det

theorem jz_det_ne {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (x : Y) (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) : (jz A w0 s i x).det ≠ 0 := by

  rw [flL_det_trans A hD hx hi (A.mem_pick x)]
  exact mul_ne_zero (hF.deriv_ne x hx) (A.g_ne _ _ _ x hi (A.mem_pick x))

theorem jz_det_trans {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (y : Y) (hy : y ∈ A.Mset w0 s De) (i j : ι)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    (jz A w0 s i y).det = (jz A w0 s j y).det * A.g A.kap i j y := flL_det_trans A hD hy hi hj

private theorem contDiffAt_det_fderiv_zLoc_of_mem_flO {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (i : ι) {v : V n} (hv : v ∈ flO A w0 i) :
    ContDiffAt ℂ ∞ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det) v := by
  have h := (flL_zLoc_contDiffOn A hD i).contDiffAt ((flL_isOpen_O A hD i).mem_nhds hv)
  exact flL_det_contDiffAt (h.fderiv_right (by simp))

theorem contDiffAt_det_jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (y : Y) (hy : y ∈ A.Mset w0 s De) (i : ι)
    (hi : y ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det) (A.chart i y) := by

  exact contDiffAt_det_fderiv_zLoc_of_mem_flO A hD i (flL_mem_O A hD hy hi)

theorem differentiableAt_det_jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (y : Y) (hy : y ∈ A.Mset w0 s De) (i : ι)
    (hi : y ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det) v := by

  filter_upwards [(flL_isOpen_O A hD i).mem_nhds (flL_mem_O A hD hy hi)] with v hv
  exact (contDiffAt_det_fderiv_zLoc_of_mem_flO A hD i hv).differentiableAt (by simp)

theorem flL_inverse {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n))
    (he : IsChart n (flatStein A hD hF).z e) (v : V n) (hv : v ∈ e.target) (i : ι)
    (hi : ((e.symm v : A.Mset w0 s De) : Y) ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : Y)) v ∧
      (∀ᶠ v' in 𝓝 v, ((e.symm v' : A.Mset w0 s De) : Y) ∈ (A.chart i).source) ∧
      ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : Y)) v
        (jz A w0 s i (e.symm v : Y) ξ) = ξ := by

  set x : Y := ((e.symm v : A.Mset w0 s De) : Y) with hxdef
  have hxM : x ∈ A.Mset w0 s De := (e.symm v).2
  have hOt : e.target ∈ 𝓝 v := e.open_target.mem_nhds hv
  have hcs : ContinuousAt (fun v' => ((e.symm v' : A.Mset w0 s De) : Y)) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : A.Mset w0 s De) : Y) ∈ (A.chart i).source :=
    hcs.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)
  have hg : ContinuousAt (fun v' => A.chart i (e.symm v' : Y)) v :=
    ((A.chart i).continuousAt hi).comp hcs
  have hfg : ∀ᶠ v' in 𝓝 v, A.zLoc w0 s i (A.chart i (e.symm v' : Y)) = v' := by
    filter_upwards [hsrc, hOt] with v' h1 h2
    rw [flL_zLoc_chart A hD h1 (denominator_ne_zero_on_chart A hD (e.symm v').2 h1)]
    have h3 : e.symm v' ∈ e.source := e.map_target h2
    have h4 := he h3
    rw [e.right_inv h2] at h4
    exact h4
  have hdet : (jz A w0 s i x).det ≠ 0 := jz_det_ne A hD hF x hxM i hi
  let f' : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (jz A w0 s i x : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hcoe : (f' : V n →L[ℂ] V n) = jz A w0 s i x := ContinuousLinearMap.ext fun ξ => rfl
  have hZ : ContDiffAt ℂ ∞ (A.zLoc w0 s i) (A.chart i x) := flL_zLoc_contDiffAt A hD hxM hi
  have hf : HasFDerivAt (A.zLoc w0 s i) (f' : V n →L[ℂ] V n) (A.chart i x) := by
    rw [hcoe]
    exact (hZ.differentiableAt (by simp)).hasFDerivAt
  have hG : HasFDerivAt (fun v' => A.chart i (e.symm v' : Y)) (f'.symm : V n →L[ℂ] V n) v :=
    HasFDerivAt.of_local_left_inverse hg hf hfg
  refine ⟨?_, hsrc, fun ξ => ?_⟩
  · have hfa : A.zLoc w0 s i (A.chart i x) = v := hfg.self_of_nhds
    have hL := hZ.to_localInverse hf (by simp)
    rw [hfa] at hL
    refine hL.congr_of_eventuallyEq ?_
    have hli := (hZ.hasStrictFDerivAt' hf (by simp)).eventually_left_inverse
    have hli' := Filter.Tendsto.eventually hg hli
    filter_upwards [hli', hfg] with v' h1 h2
    rw [h2] at h1
    exact h1.symm
  · rw [hG.fderiv]
    exact f'.symm_apply_apply ξ

theorem smooth_flat {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (u : Y → ℂ)
    (hu : ∀ x ∈ A.Mset w0 s De, ∃ i, x ∈ (A.chart i).source ∧
      ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) :
    Smooth n (flatStein A hD hF).z (fun y : A.Mset w0 s De => u y) := by

  intro e he v hv
  obtain ⟨i, hi, hu'⟩ := hu ((e.symm v : A.Mset w0 s De) : Y) (e.symm v).2
  obtain ⟨hG, hsrc, -⟩ := flL_inverse A hD hF e he v hv i hi
  have hc : ContDiffAt ℝ ∞ ((u ∘ (A.chart i).symm) ∘ fun v' => A.chart i (e.symm v' : Y)) v :=
    hu'.comp v (hG.restrict_scalars ℝ)
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hsrc] with v' h
  simp [Function.comp_apply, (A.chart i).left_inv h]

theorem smoothR_flat {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (φ : Y → ℝ)
    (hφ : ∀ x ∈ A.Mset w0 s De, ∃ i, x ∈ (A.chart i).source ∧
      ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) :
    SmoothR n (flatStein A hD hF).z (fun y : A.Mset w0 s De => φ y) := by

  unfold SmoothR
  exact smooth_flat A hD hF (fun y => (φ y : ℂ)) fun x hx => by
    obtain ⟨i, hi, h⟩ := hφ x hx
    exact ⟨i, hi, Complex.ofRealCLM.contDiff.contDiffAt.comp _ h⟩

private theorem chart_symm_eventuallyEq_of_isChart' {n : ℕ} {M : Type*} [TopologicalSpace M] {z : M → V n} {E E' : OpenPartialHomeomorph M (V n)}
    (hE : IsChart n z E) (hE' : IsChart n z E') {q : M} (hq : q ∈ E.source) (hq' : q ∈ E'.source) :
    (E.symm : V n → M) =ᶠ[𝓝 (z q)] E'.symm := by
  have h1 : z q = E q := hE hq
  have h2 : z q = E' q := hE' hq'
  have hW : IsOpen (E.source ∩ E'.source) := E.open_source.inter E'.open_source
  have hc := E.continuousAt_symm (E.map_source hq)
  rw [ContinuousAt, E.left_inv hq] at hc
  have ha : ∀ᶠ v in 𝓝 (E q), E.symm v ∈ E.source ∩ E'.source :=
    hc.eventually_mem (hW.mem_nhds ⟨hq, hq'⟩)
  have hb : E'.target ∈ 𝓝 (E q) := by
    rw [← h1, h2]
    exact E'.open_target.mem_nhds (E'.map_source hq')
  rw [h1]
  filter_upwards [ha, E.open_target.mem_nhds (E.map_source hq), hb] with v h3 h4 h5
  apply E'.injOn h3.2 (E'.map_target h5)
  rw [E'.right_inv h5, ← hE' h3.2, hE h3.1, E.right_inv h4]

private theorem d_eq_wd_comp_chart_symm' {n : ℕ} {M : Type*} [TopologicalSpace M] {z : M → V n} {E : OpenPartialHomeomorph M (V n)} (hE : IsChart n z E)
    {x : M} (hx : x ∈ E.source) (j : Fin n) (G : M → ℂ) :
    d n z j G x = wd n j (G ∘ E.symm) (z x) := by
  unfold d
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨E, hE, hx⟩
  rw [dif_pos h]
  obtain ⟨hc, hxc⟩ := Classical.choose_spec h
  apply wd_congr
  filter_upwards [chart_symm_eventuallyEq_of_isChart' hc hE hxc hx] with v hv
  simp only [Function.comp_apply, hv]

private theorem db_eq_wdb_comp_chart_symm' {n : ℕ} {M : Type*} [TopologicalSpace M] {z : M → V n} {E : OpenPartialHomeomorph M (V n)} (hE : IsChart n z E)
    {x : M} (hx : x ∈ E.source) (j : Fin n) (G : M → ℂ) :
    db n z j G x = wdb n j (G ∘ E.symm) (z x) := by
  unfold db
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨E, hE, hx⟩
  rw [dif_pos h]
  obtain ⟨hc, hxc⟩ := Classical.choose_spec h
  apply wdb_congr
  filter_upwards [chart_symm_eventuallyEq_of_isChart' hc hE hxc hx] with v hv
  simp only [Function.comp_apply, hv]

theorem levi_flat_loc {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (φ : Y → ℝ) (i : ι) (x : A.Mset w0 s De)
    (hx : (x : Y) ∈ (A.chart i).source)
    (hφ : ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) (ξ : Fin n → ℂ) :
    A.leviAt i φ x ξ =
      (Levi n (flatStein A hD hF).z (fun y : A.Mset w0 s De => φ y) x
        (fun k => jz A w0 s i x (WithLp.toLp 2 ξ) k)).re := by

  obtain ⟨E, hxE, hfE⟩ := hF.localHomeo x
  have hE : IsChart n (flatStein A hD hF).z E := fun q _ => congrFun hfE q
  have hEx : E.symm (E x) = x := E.left_inv hxE
  have hi : ((E.symm (E x) : A.Mset w0 s De) : Y) ∈ (A.chart i).source := by
    rw [hEx]; exact hx
  obtain ⟨hG, hsrc, hJ⟩ := flL_inverse A hD hF E hE (E x) (E.map_source hxE) i hi
  rw [hEx] at hJ
  have hzx : (flatStein A hD hF).z x = E x := hE hxE
  have hL : ∀ η : Fin n → ℂ, Levi n (flatStein A hD hF).z (fun y : A.Mset w0 s De => φ y) x η =
      leviV n ((fun y : A.Mset w0 s De => ((φ y : ℝ) : ℂ)) ∘ E.symm) (E x) η := by
    intro η
    unfold Levi leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [d_eq_wd_comp_chart_symm' hE hxE, hzx]
    congr 2
    apply wd_congr
    filter_upwards [E.open_target.mem_nhds (E.map_source hxE)] with v hv
    simp only [Function.comp_apply]
    rw [db_eq_wdb_comp_chart_symm' hE (E.map_target hv), hE (E.map_target hv), E.right_inv hv]
  have hU : ContDiffAt ℝ 2 (fun p => ((φ ((A.chart i).symm p) : ℝ) : ℂ))
      (A.chart i ((E.symm (E x) : A.Mset w0 s De) : Y)) := by
    rw [hEx]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hφ).of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | decide | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  have hG2 : ContDiffAt ℂ 2 (fun v' => A.chart i (E.symm v' : Y)) (E x) := hG.of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | decide | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  have hcomp : (fun y : A.Mset w0 s De => ((φ y : ℝ) : ℂ)) ∘ E.symm =ᶠ[𝓝 (E x)]
      (fun p => ((φ ((A.chart i).symm p) : ℝ) : ℂ)) ∘ (fun v' => A.chart i (E.symm v' : Y)) := by
    filter_upwards [hsrc] with v' h
    simp only [Function.comp_apply, (A.chart i).left_inv h]
  have hJ' : fderiv ℂ (fun v' => A.chart i (E.symm v' : Y)) (E x)
      (WithLp.toLp 2 (fun k => jz A w0 s i x (WithLp.toLp 2 ξ) k)) = WithLp.toLp 2 ξ := hJ _
  rw [hL, leviV_congr hcomp, flA_leviV_comp (U := fun p => ((φ ((A.chart i).symm p) : ℝ) : ℂ))
    (G := fun v' => A.chart i (E.symm v' : Y)) (y := E x) hU hG2, hJ']
  unfold WeightedAtlas.leviAt
  simp only [hEx]

theorem leviNonneg_flat {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (φ : Y → ℝ)
    (hφ : ∀ x ∈ A.Mset w0 s De, ∃ i, x ∈ (A.chart i).source ∧
      ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧
      ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) :
    LeviNonneg n (flatStein A hD hF).z (fun y : A.Mset w0 s De => φ y) := by

  intro x ξ
  obtain ⟨i, hi, hφi, hpos⟩ := hφ x x.2
  have hdet := jz_det_ne A hD hF x x.2 i hi
  let f' : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (jz A w0 s i x : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have key := levi_flat_loc A hD hF φ i x hi hφi (f'.symm (WithLp.toLp 2 ξ)).ofLp
  have h1 : jz A w0 s i x (f'.symm (WithLp.toLp 2 ξ)) = WithLp.toLp 2 ξ := f'.apply_symm_apply _
  have h2 : (fun k => jz A w0 s i x (WithLp.toLp 2 (f'.symm (WithLp.toLp 2 ξ)).ofLp) k) = ξ := by
    funext k
    rw [WithLp.toLp_ofLp, h1]
  rw [h2] at key
  rw [← key]
  exact hpos _

private theorem ofLp_apply_toLp_eq_sum_mul_basis {n : ℕ} (T : V n →L[ℂ] V n) (η : Fin n → ℂ) (b : Fin n) :
    (T (WithLp.toLp 2 η)).ofLp b = ∑ j, η j * (T (bas n j)).ofLp b := by
  have h := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (WithLp.toLp 2 η)
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
  conv_lhs => rw [← h]
  simp [map_sum, bas, smul_eq_mul]

theorem dbar_flat_loc {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (u : Y → ℂ) (i : ι) (x : A.Mset w0 s De)
    (hx : (x : Y) ∈ (A.chart i).source)
    (hu : ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) (ξ : Fin n → ℂ) :
    A.dbarAt i (fun _ => u) x ξ =
      dbarDot n (flatStein A hD hF).z (fun y : A.Mset w0 s De => u y) x
        (fun k => jz A w0 s i x (WithLp.toLp 2 ξ) k) := by

  obtain ⟨E, hxE, hfE⟩ := hF.localHomeo x
  have hE : IsChart n (flatStein A hD hF).z E := fun q _ => congrFun hfE q
  have hEx : E.symm (E x) = x := E.left_inv hxE
  have hi : ((E.symm (E x) : A.Mset w0 s De) : Y) ∈ (A.chart i).source := by
    rw [hEx]; exact hx
  obtain ⟨hG, hsrc, hJ⟩ := flL_inverse A hD hF E hE (E x) (E.map_source hxE) i hi
  rw [hEx] at hJ
  have hzx : (flatStein A hD hF).z x = E x := hE hxE
  have hU1 : DifferentiableAt ℝ (u ∘ (A.chart i).symm)
      (A.chart i ((E.symm (E x) : A.Mset w0 s De) : Y)) := by
    rw [hEx]; exact hu.differentiableAt (by simp)
  have hG1 : DifferentiableAt ℂ (fun v' => A.chart i (E.symm v' : Y)) (E x) :=
    hG.differentiableAt (by simp)
  have hcomp : (fun y : A.Mset w0 s De => u y) ∘ E.symm =ᶠ[𝓝 (E x)]
      (u ∘ (A.chart i).symm) ∘ (fun v' => A.chart i (E.symm v' : Y)) := by
    filter_upwards [hsrc] with v' h
    simp only [Function.comp_apply, (A.chart i).left_inv h]
  have step : ∀ j, db n (flatStein A hD hF).z j (fun y : A.Mset w0 s De => u y) x =
      ∑ b, wdb n b (u ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ)
        ((fderiv ℂ (fun v' => A.chart i (E.symm v' : Y)) (E x) (bas n j)).ofLp b) := by
    intro j
    rw [db_eq_wdb_comp_chart_symm' hE hxE, hzx, wdb_congr hcomp, flA_wdb_comp (U := u ∘ (A.chart i).symm)
      (G := fun v' => A.chart i (E.symm v' : Y)) (y := E x) hU1 hG1]
    simp only [hEx]
  have hJ' : fderiv ℂ (fun v' => A.chart i (E.symm v' : Y)) (E x)
      (WithLp.toLp 2 (fun k => jz A w0 s i x (WithLp.toLp 2 ξ) k)) = WithLp.toLp 2 ξ := hJ _
  unfold dbarDot WeightedAtlas.dbarAt
  simp only [step, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : ξ b = ∑ j, jz A w0 s i x (WithLp.toLp 2 ξ) j *
      (fderiv ℂ (fun v' => A.chart i (E.symm v' : Y)) (E x) (bas n j)).ofLp b := by
    have h1 := ofLp_apply_toLp_eq_sum_mul_basis (fderiv ℂ (fun v' => A.chart i (E.symm v' : Y)) (E x))
      (fun k => jz A w0 s i x (WithLp.toLp 2 ξ) k) b
    rw [hJ'] at h1
    exact h1
  rw [hb, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem leviAt_congr {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y) (hy : y ∈ (A.chart i).source)
    (h : f =ᶠ[𝓝 y] g) (ξ : Fin n → ℂ) : A.leviAt i f y ξ = A.leviAt i g y ξ := by

  unfold WeightedAtlas.leviAt
  congr 1
  apply leviV_congr
  have hc := (A.chart i).continuousAt_symm ((A.chart i).map_source hy)
  rw [ContinuousAt, (A.chart i).left_inv hy] at hc
  filter_upwards [hc.eventually h] with v hv
  simp only [hv]

theorem leviAt_add {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y)
    (hf : ContDiffAt ℝ 2 (f ∘ (A.chart i).symm) (A.chart i y))
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart i).symm) (A.chart i y)) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => f x + g x) y ξ = A.leviAt i f y ξ + A.leviAt i g y ξ := by

  unfold WeightedAtlas.leviAt
  rw [← Complex.add_re]
  congr 1
  simp only [Complex.ofReal_add]
  have hf1 : ContDiffAt ℝ 2 (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have hg1 : ContDiffAt ℝ 2 (fun v => ((g ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : wdb n k (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ) + ((g ((A.chart i).symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (A.chart i y)] fun v => wdb n k (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) v +
        wdb n k (fun v => ((g ((A.chart i).symm v) : ℝ) : ℂ)) v := by
    filter_upwards [hf1.eventually (by simp), hg1.eventually (by simp)] with v a b
    exact wdb_add (a.differentiableAt (by simp)) (b.differentiableAt (by simp))
  rw [wd_congr hw, wd_add (differentiableAt_wdb hf1) (differentiableAt_wdb hg1)]
  ring

theorem leviAt_log_normSq {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (h : Y → ℂ) (y : Y) (hy : y ∈ (A.chart i).source)
    (hh : ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (h ∘ (A.chart i).symm) v)
    (hne : h y ≠ 0) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => Real.log (‖h x‖ ^ 2)) y ξ = 0 := by

  have hp0 : h ((A.chart i).symm (A.chart i y)) ≠ 0 := by rw [(A.chart i).left_inv hy]; exact hne
  have hH' : ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (fun v => h ((A.chart i).symm v)) v := hh
  obtain ⟨t, ht, hto, hpt⟩ := eventually_nhds_iff.1 hH'
  have hHt : DifferentiableOn ℂ (fun v => h ((A.chart i).symm v)) t :=
    fun v hv => (ht v hv).differentiableWithinAt
  have hne' : ∀ᶠ v in 𝓝 (A.chart i y), h ((A.chart i).symm v) ≠ 0 :=
    (hH'.self_of_nhds).continuousAt.eventually_ne hp0
  have key : ∀ j k, wd n j (wdb n k (fun v => ((Real.log (‖h ((A.chart i).symm v)‖ ^ 2) : ℝ) : ℂ)))
      (A.chart i y) = 0 := by
    intro j k
    have hQd : DifferentiableAt ℂ (fun v => fderiv ℂ (fun v => h ((A.chart i).symm v)) v (bas n k) *
        (h ((A.chart i).symm v))⁻¹) (A.chart i y) :=
      ((ReciprocityTheory.L2DbarEstimates.C.holoDeriv n t _ hto hHt (bas n k)).differentiableAt (hto.mem_nhds hpt)).mul
        ((hH'.self_of_nhds).inv hp0)
    have hev : wdb n k (fun v => ((Real.log (‖h ((A.chart i).symm v)‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 (A.chart i y)]
        fun v => (starRingEnd ℂ) (fderiv ℂ (fun v => h ((A.chart i).symm v)) v (bas n k) *
          (h ((A.chart i).symm v))⁻¹) := by
      filter_upwards [hto.mem_nhds hpt, hne'] with v hvt hv0
      have hd : DifferentiableAt ℂ (fun v => h ((A.chart i).symm v)) v := ht v hvt
      have hdR := hd.restrictScalars ℝ
      have hN : ‖h ((A.chart i).symm v)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv0)
      rw [wdb_ofReal_comp (k := Real.log) (v := fun v => ‖h ((A.chart i).symm v)‖ ^ 2)
        (Real.differentiableAt_log hN) (by first | exact DifferentiableAt.norm_sq ℝ hdR | exact hdR.norm_sq (𝕜 := ℝ) | exact hdR.norm_sq ℂ)]
      have hsq : (fun y => (((‖h ((A.chart i).symm y)‖ ^ 2 : ℝ)) : ℂ)) =
          fun y => h ((A.chart i).symm y) * (starRingEnd ℂ) (h ((A.chart i).symm y)) := by
        funext y
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        try push_cast
        try ring
      have hcR : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (h ((A.chart i).symm y))) v :=
        Complex.conjCLE.differentiable.differentiableAt.comp v hdR
      have hc : ((‖h ((A.chart i).symm v)‖ ^ 2 : ℝ) : ℂ) =
          h ((A.chart i).symm v) * (starRingEnd ℂ) (h ((A.chart i).symm v)) := congrFun hsq v
      have hca : (starRingEnd ℂ) (h ((A.chart i).symm v)) ≠ 0 := (map_ne_zero _).2 hv0
      rw [hsq, wdb_mul hdR hcR, wdb_of_differentiableAt hd, wdb_conj hdR, wd_of_differentiableAt hd]
      simp only [Real.deriv_log, Complex.ofReal_inv, hc, map_mul, map_inv₀]
      field_simp
      ring
    rw [wd_congr hev, wd_conj (hQd.restrictScalars ℝ), wdb_of_differentiableAt hQd, map_zero]
  unfold WeightedAtlas.leviAt leviV
  simp only [key, zero_mul, Finset.sum_const_zero, Complex.zero_re]

end

end ReciprocityTheory.L2DbarEstimates.Y
