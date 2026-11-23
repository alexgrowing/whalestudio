import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContinuousOnSec

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

theorem fc_zLoc_eq {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (i : ι) (v : V n)
    (hv : v ∈ (A.chart i).target) :
    A.zLoc w0 s i v = A.zmap w0 s ((A.chart i).symm v) := by
  have secS : ∀ k i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      s k i y = A.g L i j y * s k j y := by
    intro k i j y hi hj
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have hy : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv
  unfold WeightedAtlas.zLoc WeightedAtlas.zmap
  congr 1
  funext k
  rw [secS k i (A.pick _) _ hy (A.mem_pick _), secW i (A.pick _) _ hy (A.mem_pick _),
    mul_div_mul_left _ _ (A.g_ne L i (A.pick _) _ hy (A.mem_pick _))]

theorem denominator_ne_zero_on_set {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) : w0 i y ≠ 0 := by
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  rw [secW i (A.pick y) y hi (A.mem_pick y)]
  exact mul_ne_zero (A.g_ne L i (A.pick y) y hi (A.mem_pick y)) hy.1

theorem fc_isOpen_O {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (i : ι) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  have secS : ∀ k i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      s k i y = A.g L i j y * s k j y := by
    intro k i j y hi hj
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have hw : DifferentiableOn ℂ (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    simpa using hs.1 i
  have hsk : ∀ k, DifferentiableOn ℂ (s k i ∘ (A.chart i).symm) (A.chart i).target := by
    intro k
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    simpa using hs.1 i
  set O1 := (A.chart i).target ∩ (fun v => w0 i ((A.chart i).symm v)) ⁻¹' {0}ᶜ with hO1def
  have hO1 : IsOpen O1 := hw.continuousOn.isOpen_inter_preimage (A.chart i).open_target
    isOpen_compl_singleton
  have hzd : ∀ k, DifferentiableOn ℂ (fun v => (A.zLoc w0 s i v).ofLp k) O1 := by
    intro k
    have h1 : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) O1 :=
      (hsk k).mono Set.inter_subset_left
    have h2 : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) O1 :=
      hw.mono Set.inter_subset_left
    have h3 := h1.mul (h2.inv fun v (hv : v ∈ O1) => hv.2)
    refine h3.congr fun v _ => ?_
    simp [WeightedAtlas.zLoc, div_eq_mul_inv]
  have hset : (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De =
      O1 ∩ (fun v => MvPolynomial.eval (fun k => A.zLoc w0 s i v k) De) ⁻¹' {0}ᶜ := by
    ext v
    constructor
    · rintro ⟨hv, hM⟩
      refine ⟨⟨hv, denominator_ne_zero_on_set A hD hM i ((A.chart i).map_target hv)⟩, ?_⟩
      show MvPolynomial.eval _ De ≠ 0
      rw [fc_zLoc_eq A hD i v hv]
      exact hM.2
    · rintro ⟨⟨hv, hw0⟩, hev⟩
      refine ⟨hv, ?_, ?_⟩
      · intro h0
        apply hw0
        show w0 i ((A.chart i).symm v) = 0
        rw [secW i (A.pick _) _ ((A.chart i).map_target hv) (A.mem_pick _), h0, mul_zero]
      · have h1 : MvPolynomial.eval (fun k => A.zLoc w0 s i v k) De ≠ 0 := hev
        rw [fc_zLoc_eq A hD i v hv] at h1
        exact h1
  rw [hset]
  have hc : ContinuousOn (fun v => fun k => A.zLoc w0 s i v k) O1 :=
    continuousOn_pi.mpr fun k => (hzd k).continuousOn
  exact ((MvPolynomial.continuous_eval De).comp_continuousOn hc).isOpen_inter_preimage hO1
    isOpen_compl_singleton

theorem fc_zLoc_contDiffOn {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (i : ι) :
    ContDiffOn ℂ ∞ (A.zLoc w0 s i) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  have secS : ∀ k i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      s k i y = A.g L i j y * s k j y := by
    intro k i j y hi hj
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have hw : DifferentiableOn ℂ (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    simpa using hs.1 i
  have hsk : ∀ k, DifferentiableOn ℂ (s k i ∘ (A.chart i).symm) (A.chart i).target := by
    intro k
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    simpa using hs.1 i
  set O1 := (A.chart i).target ∩ (fun v => w0 i ((A.chart i).symm v)) ⁻¹' {0}ᶜ with hO1def
  have hO1 : IsOpen O1 := hw.continuousOn.isOpen_inter_preimage (A.chart i).open_target
    isOpen_compl_singleton
  have hzd : ∀ k, DifferentiableOn ℂ (fun v => (A.zLoc w0 s i v).ofLp k) O1 := by
    intro k
    have h1 : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) O1 :=
      (hsk k).mono Set.inter_subset_left
    have h2 : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) O1 :=
      hw.mono Set.inter_subset_left
    have h3 := h1.mul (h2.inv fun v (hv : v ∈ O1) => hv.2)
    refine h3.congr fun v _ => ?_
    simp [WeightedAtlas.zLoc, div_eq_mul_inv]
  have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De ⊆ O1 :=
    fun v hv => ⟨hv.1, denominator_ne_zero_on_set A hD hv.2 i ((A.chart i).map_target hv.1)⟩
  have hopen := fc_isOpen_O A (De := De) hD i
  rw [contDiffOn_euclidean]
  intro k
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hopen ((hzd k).mono hsub)

theorem fc_det_jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i j : ι) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) :
    (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det = (fderiv ℂ (A.zLoc w0 s j) (A.chart j y)).det * A.g A.kap i j y := by
  have hT : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
    simp only [Function.comp, (A.chart i).left_inv hi]
  have hov : IsOpen (ovl A.chart i j) :=
    (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
  have hx0ov : A.chart i y ∈ ovl A.chart i j := by
    refine ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i y) ∈ (A.chart j).source
    rw [(A.chart i).left_inv hi]
    exact hj
  have hev : A.zLoc w0 s i =ᶠ[𝓝 (A.chart i y)] A.zLoc w0 s j ∘ (A.chart j ∘ (A.chart i).symm) := by
    filter_upwards [hov.mem_nhds hx0ov] with v hv
    simp only [Function.comp]
    rw [fc_zLoc_eq A hD i v hv.1, fc_zLoc_eq A hD j _ ((A.chart j).map_source hv.2),
      (A.chart j).left_inv hv.2]
  have hdT : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
    (A.holo_trans i j).differentiableAt (hov.mem_nhds hx0ov)
  have hdz : DifferentiableAt ℂ (A.zLoc w0 s j) ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
    rw [hT]
    have hO := fc_isOpen_O A (De := De) hD j
    have hm : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' A.Mset w0 s De := by
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j y) ∈ A.Mset w0 s De
      rw [(A.chart j).left_inv hj]
      exact hy
    exact ((fc_zLoc_contDiffOn A hD j).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hm)
  rw [hev.fderiv_eq, fderiv_comp (A.chart i y) hdz hdT, hT, A.g_kap i j y hi hj]
  change LinearMap.det (((fderiv ℂ (A.zLoc w0 s j) (A.chart j y)).comp
      (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) =
    LinearMap.det ((fderiv ℂ (A.zLoc w0 s j) (A.chart j y)) : V n →ₗ[ℂ] V n) *
      LinearMap.det ((fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) : V n →ₗ[ℂ] V n)
  exact LinearMap.det_comp ((fderiv ℂ (A.zLoc w0 s j) (A.chart j y)) : V n →ₗ[ℂ] V n)
    ((fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) : V n →ₗ[ℂ] V n)

theorem fc_jz_det_ne {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) {y : Y} (hy : y ∈ A.Mset w0 s De) (i : ι)
    (hi : y ∈ (A.chart i).source) : (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det ≠ 0 := by
  rw [fc_det_jz A hD hy i (A.pick y) hi (A.mem_pick y)]
  exact mul_ne_zero (hF.deriv_ne y hy) (A.g_ne A.kap i (A.pick y) y hi (A.mem_pick y))

theorem fc_chart_fwd {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x),
      ((e.symm (A.zLoc w0 s i v) : A.Mset w0 s De) : Y) = (A.chart i).symm v := by
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
    refine ⟨(A.chart i).map_source hxi, ?_⟩
    show (A.chart i).symm (A.chart i x) ∈ A.Mset w0 s De
    rw [(A.chart i).left_inv hxi]
    exact x.2
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.mp e.open_source
  have hxU : (x : Y) ∈ U := by
    have hx : x ∈ Subtype.val ⁻¹' U := by rw [hUe]; exact hxe
    exact hx
  have hcont : ∀ᶠ v in 𝓝 (A.chart i x), (A.chart i).symm v ∈ U := by
    apply ((A.chart i).continuousAt_symm ((A.chart i).map_source hxi)).preimage_mem_nhds
    rw [(A.chart i).left_inv hxi]
    exact hU.mem_nhds hxU
  filter_upwards [hO.mem_nhds hmO, hcont] with v hvO hvU
  have hp : (⟨(A.chart i).symm v, hvO.2⟩ : A.Mset w0 s De) ∈ e.source := by
    rw [← hUe]
    exact hvU
  have hz : A.zLoc w0 s i v = e ⟨(A.chart i).symm v, hvO.2⟩ := by
    rw [fc_zLoc_eq A hD i v hvO.1]
    exact he hp
  rw [hz, e.left_inv hp]

theorem fc_zLoc_chart {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i x) = e x := by
  rw [fc_zLoc_eq A hD i _ ((A.chart i).map_source hxi), (A.chart i).left_inv hxi]
  exact he hxe

theorem fc_mem_O {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (x : A.Mset w0 s De) (i : ι)
    (hxi : (x : Y) ∈ (A.chart i).source) :
    A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
  refine ⟨(A.chart i).map_source hxi, ?_⟩
  show (A.chart i).symm (A.chart i x) ∈ A.Mset w0 s De
  rw [(A.chart i).left_inv hxi]
  exact x.2

theorem fc_chart_inv {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    ∃ G : V n → V n, ContDiffAt ℂ ∞ G (e x) ∧ G (e x) = A.chart i x ∧
      ∀ᶠ w in 𝓝 (e x), ((e.symm w : A.Mset w0 s De) : Y) = (A.chart i).symm (G w) := by
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO := fc_mem_O A x i hxi
  have hcd : ContDiffAt ℂ ∞ (A.zLoc w0 s i) (A.chart i x) :=
    (fc_zLoc_contDiffOn A hD i).contDiffAt (hO.mem_nhds hmO)
  have hdet := fc_jz_det_ne A hD hF x.2 i hxi
  let f' : V n ≃L[ℂ] V n :=
    (fderiv ℂ (A.zLoc w0 s i) (A.chart i x)).toContinuousLinearEquivOfDetNeZero hdet
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := WithTop.coe_ne_zero.mpr (by simp)
  have hf' : HasFDerivAt (A.zLoc w0 s i) (f' : V n →L[ℂ] V n) (A.chart i x) := by
    simp only [f', ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hcd.differentiableAt hn).hasFDerivAt
  have hs : HasStrictFDerivAt (A.zLoc w0 s i) (f' : V n →L[ℂ] V n) (A.chart i x) :=
    hcd.hasStrictFDerivAt' hf' hn
  have hloc := hcd.to_localInverse hf' hn
  have hzx : A.zLoc w0 s i (A.chart i x) = e x := fc_zLoc_chart A hD e he x hxe i hxi
  have hsymmc : ContinuousAt (fun w => ((e.symm w : A.Mset w0 s De) : Y)) (e x) :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm (e.map_source hxe))
  have hGc : Filter.Tendsto (fun w => A.chart i (e.symm w : Y)) (𝓝 (e x)) (𝓝 (A.chart i x)) := by
    have h := ((A.chart i).continuousAt hxi).comp_of_eq hsymmc (by simp [e.left_inv hxe])
    unfold ContinuousAt at h
    simp only [Function.comp_apply, e.left_inv hxe] at h
    exact h
  have hGx : A.chart i (e.symm (e x) : Y) = A.chart i x := by rw [e.left_inv hxe]
  have hev1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ e.source ∧ (e.symm w : Y) ∈ (A.chart i).source := by
    have h1 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds (e.map_source hxe)
    have h2 : ∀ᶠ w in 𝓝 (e x), ((e.symm w : A.Mset w0 s De) : Y) ∈ (A.chart i).source := by
      apply hsymmc.preimage_mem_nhds
      simp only [e.left_inv hxe]
      exact (A.chart i).open_source.mem_nhds hxi
    filter_upwards [h1, h2] with w hw1 hw2
    exact ⟨e.map_target hw1, hw2⟩
  have hright : ∀ᶠ w in 𝓝 (e x), A.zLoc w0 s i (A.chart i (e.symm w : Y)) = w := by
    filter_upwards [hev1, e.open_target.mem_nhds (e.map_source hxe)] with w hw hwt
    rw [fc_zLoc_chart A hD e he (e.symm w) hw.1 i hw.2, e.right_inv hwt]
  have hleft := hGc.eventually hs.eventually_left_inverse
  refine ⟨fun w => A.chart i (e.symm w : Y), ?_, hGx, ?_⟩
  · have heq : (fun w => A.chart i (e.symm w : Y)) =ᶠ[𝓝 (e x)] hcd.localInverse hf' hn := by
      filter_upwards [hleft, hright] with w h1 h2
      rw [h2] at h1
      exact h1.symm
    rw [hzx] at hloc
    exact hloc.congr_of_eventuallyEq heq
  · filter_upwards [hev1] with w hw
    rw [(A.chart i).left_inv hw.2]

end

end ReciprocityTheory.L2DbarEstimates.Y
