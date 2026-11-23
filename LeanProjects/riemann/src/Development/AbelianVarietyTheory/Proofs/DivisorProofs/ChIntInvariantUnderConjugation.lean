import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.ConjChart GlobalTheory.ShFam
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb)
open scoped ENNReal

namespace GlobalTheory.ChernConj

theorem conjV_conjV (n : ℕ) (v : V n) : conjV n (conjV n v) = v := by
  ext a
  simp [conjV_apply]

theorem cHess_comp_conjV (n : ℕ) (g : V n → ℝ) (y : V n) :
    cHess n ((fun v => (g v : ℂ)) ∘ conjV n) y =
      (cHess n (fun v => (g v : ℂ)) (conjV n y)).map (starRingEnd ℂ) := by
  set G : V n → ℂ := fun v => (g v : ℂ) with hGdef
  have hG : ∀ k, wd n k G = fun w => starRingEnd ℂ (wdb n k G w) := fun k => by
    have e : G = fun w => starRingEnd ℂ (G w) := funext fun w => (Complex.conj_ofReal _).symm
    funext w
    conv_lhs => rw [e]
    exact ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n k G w
  have h1 : ∀ k, wdb n k (G ∘ conjV n) = (wd n k G) ∘ conjV n := fun k =>
    funext fun w => wdb_comp_conjV n k G w
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.map_apply]
  rw [h1, wd_comp_conjV, hG, ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj']

theorem det_re_cHess_comp_conjV (n : ℕ) (g : V n → ℝ) (y : V n) :
    (cHess n ((fun v => (g v : ℂ)) ∘ conjV n) y).det.re =
      (cHess n (fun v => (g v : ℂ)) (conjV n y)).det.re := by
  rw [cHess_comp_conjV]
  have := RingHom.map_det (starRingEnd ℂ) (cHess n (fun v => (g v : ℂ)) (conjV n y))
  rw [RingHom.mapMatrix_apply] at this
  rw [← this, Complex.conj_re]

end GlobalTheory.ChernConj

namespace GlobalTheory.ChernConj

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB X} {D : ℕ}
  {φ : Weight p σ B} {φ' : Weight p σ' B}

theorem chernDens_conj (h : σ' = (starRingEnd ℂ).comp σ) (hc : φ.IsConj φ') (h' : φ'.IsCInf)
    (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) :
    (conjChart h a).chernDens φ' (conjPts p h y) = a.chernDens φ y := by
  set i := pick φ.isLB y with hidef
  have hi : y ∈ ptsIn p σ (B.U i) := mem_pick φ.isLB y
  have e : (conjPts p h y).1 = spMap (starRingEnd ℂ) ≫ y.1 := rfl
  have hy' : conjPts p h y ∈ (conjChart h a).e.source := by
    change (conjPts p h).symm (conjPts p h y) ∈ a.e.source
    rw [Homeomorph.symm_apply_apply]
    exact hy
  have e₁ : (conjChart h a).e (conjPts p h y) = conjV D (a.e y) := by
    change conjCoord D (a.e ((conjPts p h).symm (conjPts p h y))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have ho : IsOpen (a.e.target ∩ a.e.symm ⁻¹' ptsIn p σ (B.U i)) := isOpen_over a.e (isOpen_ptsIn _)
  have hm : a.e y ∈ a.e.target ∩ a.e.symm ⁻¹' ptsIn p σ (B.U i) := mem_over a.e hy hi
  have hm' : conjV D (a.e y) ∈ conjV D ⁻¹' (a.e.target ∩ a.e.symm ⁻¹' ptsIn p σ (B.U i)) := by
    rw [mem_preimage, conjV_conjV]
    exact hm
  have e₂ : (fun v => (φ'.φ i ((conjChart h a).e.symm v) : ℂ)) =ᶠ[𝓝 (conjV D (a.e y))]
      (fun v => (φ.φ i (a.e.symm v) : ℂ)) ∘ conjV D := by
    filter_upwards [(ho.preimage (conjV D).continuous).mem_nhds hm'] with v hv
    change (φ'.φ i (conjPts p h (a.e.symm (conjCoord D v))) : ℂ) = (φ.φ i (a.e.symm (conjV D v)) : ℂ)
    rw [hc i _ _ rfl hv.2]
  rw [(conjChart h a).chernDens_eq h' hy' (mem_ptsIn_of_conj e hi), AlgChart.chernDens, AlgChart.hess,
    e₁, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e₂, det_re_cHess_comp_conjV D (fun v => φ.φ i (a.e.symm v)),
    conjV_conjV]
  rfl

end GlobalTheory.ChernConj

namespace GlobalTheory.ChernConj

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB X} {D : ℕ}
  {φ : Weight p σ B} {φ' : Weight p σ' B}

theorem measurePreserving_conjCoord' (n : ℕ) : MeasurePreserving (conjCoord n) := by
  have e : (conjCoord n : V n → V n) = conjV n := rfl
  rw [e]
  exact (conjV n).measurePreserving

variable [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts p σ')]

theorem chernPart_conj (h : σ' = (starRingEnd ℂ).comp σ) (hc : φ.IsConj φ') (hφ : φ.IsCInf)
    (h' : φ'.IsCInf) (ε : ℤˣ) :
    φ'.chernPart D ε = (φ.chernPart D ε).map (conjPts p h) := by
  set J : CxPts p σ ≃ₜ CxPts p σ' := conjPts p h with hJ
  have hJm : Measurable J := J.continuous.measurable
  have h2 : σ = (starRingEnd ℂ).comp σ' := RingHom.ext fun x => by rw [h]; simp
  have hJs : ∀ z, J.symm z = conjPts p h2 z := fun z => Subtype.ext rfl
  have hS : ∀ a : AlgChart p σ D, IsOpen (conjChart h a).e.source := fun a => (conjChart h a).e.open_source
  have hmemS : ∀ (a : AlgChart p σ D) y, J y ∈ (conjChart h a).e.source ↔ y ∈ a.e.source := fun a y => by
    change J.symm (J y) ∈ a.e.source ↔ _
    rw [Homeomorph.symm_apply_apply]
  have hloc : ∀ (a : AlgChart p σ D) (A : Set (CxPts p σ')), MeasurableSet A → A ⊆ (conjChart h a).e.source →
      φ'.chernPart D ε A = (φ.chernPart D ε).map J A := fun a A hA hs => by
    have hA' : MeasurableSet (J ⁻¹' A) := hJm hA
    have hs' : J ⁻¹' A ⊆ a.e.source := fun y hy => (hmemS a y).1 (hs hy)
    rw [Measure.map_apply hJm hA, Weight.chernPart_apply h' ε (conjChart h a) hA hs,
      Weight.chernPart_apply hφ ε a hA' hs']
    have him : (conjChart h a).e '' A = conjCoord D '' (a.e '' (J ⁻¹' A)) := by
      rw [image_image]
      ext v
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨J.symm z, ?_, rfl⟩
        show J (J.symm z) ∈ A
        rw [J.apply_symm_apply]
        exact hz
      · rintro ⟨y, hy, rfl⟩
        refine ⟨J y, hy, ?_⟩
        change conjCoord D (a.e (J.symm (J y))) = _
        rw [Homeomorph.symm_apply_apply]
    rw [him, ← (measurePreserving_conjCoord' D).setLIntegral_comp_emb (conjCoord D).measurableEmbedding]
    refine setLIntegral_congr_fun (measurableSet_image a.e hA' hs') ?_
    rintro _ ⟨y, hy, rfl⟩
    have e : (conjChart h a).e.symm (conjCoord D (a.e y)) = J y := by
      change J (a.e.symm ((conjCoord D).symm (conjCoord D (a.e y)))) = J y
      rw [Homeomorph.symm_apply_apply, a.e.left_inv (hs' hy)]
    simp only []
    rw [e, a.e.left_inv (hs' hy), chernDens_conj h hc h' a (hs' hy)]
  have hU : IsOpen (⋃ a : AlgChart p σ D, (conjChart h a).e.source) := isOpen_iUnion hS
  have hμ : φ'.chernPart D ε (⋃ a : AlgChart p σ D, (conjChart h a).e.source)ᶜ = 0 :=
    Weight.chernPart_eq_zero ε hU.measurableSet.compl fun c' => by
      rw [Set.disjoint_compl_right_iff_subset]
      intro z hz
      refine mem_iUnion.2 ⟨conjChart h2 c', ?_⟩
      change (conjPts p h2).symm (J.symm z) ∈ c'.e.source
      rw [hJs, Homeomorph.symm_apply_apply]
      exact hz
  have hν : (φ.chernPart D ε).map J (⋃ a : AlgChart p σ D, (conjChart h a).e.source)ᶜ = 0 := by
    rw [Measure.map_apply hJm hU.measurableSet.compl]
    refine Weight.chernPart_eq_zero ε (hJm hU.measurableSet.compl) fun a => ?_
    rw [Set.disjoint_left]
    intro y hy hyU
    exact hyU (mem_iUnion.2 ⟨a, (hmemS a y).2 hy⟩)
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun a : AlgChart p σ D => (conjChart h a).e.source) hS
  have hres : (φ'.chernPart D ε).restrict (⋃ a : AlgChart p σ D, (conjChart h a).e.source) =
      ((φ.chernPart D ε).map J).restrict (⋃ a : AlgChart p σ D, (conjChart h a).e.source) := by
    rw [← hTS]
    refine (Measure.restrict_biUnion_congr hT).2 fun a _ => ?_
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact hloc a _ (hA.inter (hS a).measurableSet) inter_subset_right
  rw [← Measure.restrict_eq_self_of_ae_mem (μ := φ'.chernPart D ε) (ae_iff.2 hμ), hres,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hν)]

end GlobalTheory.ChernConj

open GlobalTheory GlobalTheory.ArInt GlobalTheory.ChernConj in

theorem GlobalTheory.ArInt.chInt_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p →
    ∀ (N : HermLB p) (D : ℕ) (f f' : ∀ σ : k →+* ℂ, CxPts p σ → ℝ),
      (∀ (σ σ' : k →+* ℂ) (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
        f' σ' y' = f σ y) → chInt N D f' = chInt N D f := by
  intro k _ X p hp N D f f' hf
  let c : (k →+* ℂ) ≃ (k →+* ℂ) :=
    { toFun := fun σ => (starRingEnd ℂ).comp σ
      invFun := fun σ => (starRingEnd ℂ).comp σ
      left_inv := fun σ => RingHom.ext fun x => by simp
      right_inv := fun σ => RingHom.ext fun x => by simp }
  rw [chInt, chInt, ← finsum_comp_equiv c (f := fun σ => (N.φ σ).chernInt D Set.univ (f' σ))]
  refine finsum_congr fun σ => ?_
  have := secondCountableTopology_of_isProjOver σ hp
  have := secondCountableTopology_of_isProjOver ((starRingEnd ℂ).comp σ) hp
  change (N.φ ((starRingEnd ℂ).comp σ)).chernInt D Set.univ (f' ((starRingEnd ℂ).comp σ)) = _
  have hfe : ∀ y : CxPts p σ, f' ((starRingEnd ℂ).comp σ) (conjPts p rfl y) = f σ y :=
    fun y => hf σ _ y _ rfl
  simp only [Weight.chernInt, Measure.restrict_univ,
    chernPart_conj rfl (N.conj σ _) (N.cInf σ) (N.cInf _)]
  have hm (μ : Measure (CxPts p σ)) : μ.map (conjPts p (σ := (starRingEnd ℂ).comp σ) (σ' := σ) rfl) =
      μ.map (conjPts p (σ := (starRingEnd ℂ).comp σ) (σ' := σ) rfl).toMeasurableEquiv := rfl
  rw [hm, hm, integral_map_equiv, integral_map_equiv]
  simp only [Homeomorph.toMeasurableEquiv_coe, hfe]
