import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentDimAndBaseDim
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentHolomorphicBoundedDomainStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

namespace GlobalTheory.UnifNull

open Set in

theorem iSup_apply_eq_zero {Z : Type*} [MeasurableSpace Z] {ι : Type*} (μ : ι → Measure Z) {T : Set Z}
    (hT : MeasurableSet T) (h : ∀ i, μ i T = 0) : (⨆ i, μ i) T = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Tᶜ := iSup_le fun i => Measure.le_iff.2 fun B hB => by
    rw [Measure.restrict_apply hB, ← measure_inter_add_diff B hT, diff_eq,
      measure_mono_null inter_subset_right (h i), zero_add]
    exact Measure.le_iff'.1 (le_iSup μ i) _
  refine le_antisymm ((Measure.le_iff'.1 hle T).trans ?_) (zero_le)
  rw [Measure.restrict_apply hT, inter_compl_self, measure_empty]

open Set in

theorem glueNull : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (ρ : AlgChart p σ D → CxPts p σ → ENNReal) (S : Set (CxPts p σ)), (∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ S)) = 0) → glueMeas (fun c : AlgChart p σ D => c.e) ρ S = 0 := by
  intro k _ Y p σ D _ ρ S hS
  classical
  obtain ⟨I, hIc, hI⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
  let Z : AlgChart p σ D → Set (ReciprocityTheory.L2DbarEstimates.V D) := fun c => toMeasurable volume (c.e '' (c.e.source ∩ S))
  have hZ : ∀ c, volume (Z c) = 0 := fun c => (measure_toMeasurable _).trans (hS c)
  have hTm : ∀ c : AlgChart p σ D, MeasurableSet (c.e.source ∩ c.e ⁻¹' Z c) := by
    intro c
    have hm := (c.e.continuousOn.measurable_piecewise (continuousOn_const (c := (0 : ReciprocityTheory.L2DbarEstimates.V D)))
      c.e.open_source.measurableSet) (measurableSet_toMeasurable volume (c.e '' (c.e.source ∩ S)))
    convert c.e.open_source.measurableSet.inter hm using 1
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> simpa [Set.piecewise_eq_of_mem _ _ _ h1] using h2
  let T : Set (CxPts p σ) := (⋃ c : AlgChart p σ D, c.e.source)ᶜ ∪ ⋃ c ∈ I, (c.e.source ∩ c.e ⁻¹' Z c)
  have hT : MeasurableSet T :=
    (isOpen_iUnion fun c : AlgChart p σ D => c.e.open_source).measurableSet.compl.union
      (MeasurableSet.biUnion hIc fun c _ => hTm c)
  have hST : S ⊆ T := by
    intro y hy
    by_cases hO : y ∈ ⋃ c : AlgChart p σ D, c.e.source
    · right
      rw [← hI] at hO
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hO
      exact mem_biUnion hc ⟨hyc, subset_toMeasurable _ _ ⟨y, ⟨hyc, hy⟩, rfl⟩⟩
    · exact Or.inl hO
  have hc0 : ∀ c : AlgChart p σ D, chartMeas c.e (ρ c) T = 0 := by
    intro c
    rw [chartMeas_apply _ _ hT]
    refine setLIntegral_measure_zero _ _ ?_
    have hsub : c.e '' (c.e.source ∩ T) ⊆ ⋃ c' ∈ I, (c.e ∘ c'.e.symm) ''
        (Z c' ∩ (c'.e.target ∩ c'.e.symm ⁻¹' c.e.source)) := by
      rintro _ ⟨y, ⟨hy, hyT⟩, rfl⟩
      rcases hyT with hyO | hyT
      · exact (hyO (mem_iUnion.2 ⟨c, hy⟩)).elim
      obtain ⟨c', hc', hy1, hy2⟩ := mem_iUnion₂.1 hyT
      refine mem_biUnion hc' ⟨c'.e y, ⟨hy2, c'.e.map_source hy1, ?_⟩, ?_⟩
      · simp only [mem_preimage, c'.e.left_inv hy1]; exact hy
      · simp only [Function.comp_apply, c'.e.left_inv hy1]
    refine measure_mono_null hsub ((measure_biUnion_null_iff hIc).2 fun c' _ => ?_)
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (((AlgChart.holo_trans c' c).restrictScalars ℝ).mono inter_subset_right)
      (measure_mono_null inter_subset_left (hZ c'))
  exact measure_mono_null hST (iSup_apply_eq_zero _ hT hc0)

open Set in

theorem volume_null_of_muD {ι : Type} [Fintype ι] {p q : ℕ} {N : Set (ι × Fin p × Fin q → ℂ)}
    (hN : N ⊆ DomFlat ι p q) (h0 : muD ι p q N = 0) : volume N = 0 := by
  have hc : ∀ i : ι, Continuous fun v : ι × Fin p × Fin q → ℂ => (hQ (unflat v i)).det.re := by
    intro i
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    have hu : Continuous fun v : ι × Fin p × Fin q → ℂ => unflat v i :=
      continuous_pi fun a => continuous_pi fun b => continuous_apply (i, a, b)
    unfold hQ
    exact continuous_const.sub (Continuous.matrix_mul (Continuous.matrix_conjTranspose hu) hu)
  have hm : Measurable fun v : ι × Fin p × Fin q → ℂ =>
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
    simp only [zpow_neg, zpow_natCast]
    exact ((hc i).measurable.pow_const _).inv
  have hpos : ∀ v ∈ DomFlat ι p q,
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) ≠ 0 := by
    intro v hv
    refine (ENNReal.ofReal_pos.2 (Finset.prod_pos fun i _ => zpow_pos ?_ _)).ne'
    have h := (hv i : (1 - (unflat v i)ᴴ * unflat v i).PosDef).det_pos
    exact (Complex.pos_iff.1 h).1
  rw [muD, withDensity_apply_eq_zero' hm.aemeasurable,
    Measure.restrict_apply' GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.measurableSet] at h0
  refine measure_mono_null ?_ h0
  intro v hv
  exact ⟨⟨hpos v (hN hv), hv⟩, hN hv⟩

open Set in

theorem chart_image_null {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ι : Type} [Fintype ι] (c : AlgChart p σ D) (ψ : (ι → ℂ) → CxPts p σ) {s : Set (ι → ℂ)}
    (hD : D = Fintype.card ι) (hs : volume s = 0)
    (hψ : ∀ a, DifferentiableOn ℂ (ev p σ c.U (c.x a) ∘ ψ) (s ∩ ψ ⁻¹' ptsIn p σ c.U)) :
    volume (c.e '' (c.e.source ∩ ψ '' s)) = 0 := by
  set t := s ∩ ψ ⁻¹' c.e.source with ht
  have e1 : c.e '' (c.e.source ∩ ψ '' s) = (c.e ∘ ψ) '' t := by
    ext y; constructor
    · rintro ⟨_, ⟨h1, w, hw, rfl⟩, rfl⟩; exact ⟨w, ⟨hw, h1⟩, rfl⟩
    · rintro ⟨w, ⟨hw, h1⟩, rfl⟩; exact ⟨ψ w, ⟨h1, w, hw, rfl⟩, rfl⟩
  have hd : DifferentiableOn ℂ (c.e ∘ ψ) t :=
    differentiableOn_euclidean.2 fun a => ((hψ a).mono fun w hw => ⟨hw.1, c.source_subset hw.2⟩).congr
      fun w hw => c.apply_eq _ hw.2 a
  have hfin : Module.finrank ℝ (ι → ℂ) = Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V D) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ι → ℂ), ← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V D)]
    simp [hD]
  let L : (ι → ℂ) ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V D := ContinuousLinearEquiv.ofFinrankEq hfin
  have h1 : volume ((L.symm ∘ (c.e ∘ ψ)) '' t) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (L.symm.differentiable.comp_differentiableOn (hd.restrictScalars ℝ))
      (measure_mono_null inter_subset_left hs)
  have e2 : (c.e ∘ ψ) '' t = L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t) := by
    rw [← L.image_eq_preimage_symm, image_image]; simp
  haveI : (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))).IsAddHaarMeasure :=
    L.symm.isAddHaarMeasure_map volume
  have hac := Measure.absolutelyContinuous_isAddHaarMeasure
    (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))) volume
  rw [e1, e2]
  calc volume (L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t))
      = Measure.map L.symm volume ((L.symm ∘ (c.e ∘ ψ)) '' t) :=
        (L.symm.toHomeomorph.toMeasurableEquiv.map_apply _).symm
    _ = 0 := hac h1

theorem image_null : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ N ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) N = 0 → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' N) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ N hN h0
  have hH := GlobalTheory.T.uniformisationComponent_holomorphic_boundedDomain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hv := volume_null_of_muD hN h0
  have hdim : X.dim = Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) := by
    rw [(GlobalTheory.FlagBaseDim.dims E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL).2]
    have h1 := ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.two_card_Psi (U.X k)
    have h2 : Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
      rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.PeriodCoord.card_cmType H
    have h3 : Fintype.card (GlobalTheory.AllWt.Psi H) = Fintype.card (U.X k).Ψ := by omega
    simp only [Fintype.card_prod, Fintype.card_fin, h3, Nat.add_sub_cancel_left]
  unfold chernTopPart
  exact glueNull X.str (σ.comp e.toRingHom) X.dim _ _ fun ch =>
    chart_image_null ch ψ hdim hv fun a => (hH ch.U (ch.x a)).mono fun w hw => ⟨hN hw.1, hw.2⟩

end GlobalTheory.UnifNull
