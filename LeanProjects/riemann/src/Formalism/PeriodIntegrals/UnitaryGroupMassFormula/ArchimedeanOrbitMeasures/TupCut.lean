import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensNu
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def PsiC {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ (KapI X) :=
  tupCoord X (κ z.1 • rmulT X (a (eH.symm z.2)) (Y0 X u'))

def PolarChartContDiffAt {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (a : HmI X → MfI X) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) : Prop :=
  ContDiffAt ℝ 1 (PsiC X u' a κ eH) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT))

open Classical in

def PsiDet {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (a : HmI X → MfI X) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ) : Prop :=
  ∃ (Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃L[ℝ] EuclideanSpace ℝ (KapI X)) (Dv : ℝ),
    fderiv ℝ (PsiC X u' a κ eH) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) =
      (Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) →L[ℝ] EuclideanSpace ℝ (KapI X)) ∧
    0 < Dv ∧
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map Φ = ENNReal.ofReal Dv • volume ∧
    Real.sqrt |(matI X).det| / (Dv * cν) = tVal X u'

theorem tVal_pos {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : 0 < tVal X u' := by
  have ht : 0 < Tw u' := by
    unfold Tw
    exact_mod_cast (D.mem u').A.T_prime.pos
  exact pow_pos ht _

theorem loc_glue {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F) (z0 : E) (Φ : E ≃L[ℝ] F)
    (h1 : ContDiffAt ℝ 1 f z0) (hd : fderiv ℝ f z0 = (Φ : E →L[ℝ] F)) :
    ∃ U ∈ 𝓝 z0, (∀ z ∈ U, HasFDerivWithinAt (Φ.symm ∘ f) ((Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z)) U z) ∧
      Set.InjOn (Φ.symm ∘ f) U ∧
      ContinuousAt (fun z => |((Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z)).det|) z0 ∧
      (Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z0) = ContinuousLinearMap.id ℝ E := by
  have hs := h1.hasStrictFDerivAt (by norm_num)
  rw [hd] at hs
  have hev := h1.eventually (by simp)
  have hPc : (hs.toOpenPartialHomeomorph f : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hsrc : (hs.toOpenPartialHomeomorph f).source ∈ 𝓝 z0 :=
    (hs.toOpenPartialHomeomorph f).open_source.mem_nhds hs.mem_toOpenPartialHomeomorph_source
  refine ⟨(hs.toOpenPartialHomeomorph f).source ∩ {z | ContDiffAt ℝ 1 f z}, inter_mem hsrc hev, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ((Φ.symm.hasFDerivAt).comp z
      (((show ContDiffAt ℝ 1 f z from hz.2).differentiableAt one_ne_zero).hasFDerivAt)).hasFDerivWithinAt
  · intro z hz z' hz' e
    have e' : f z = f z' := Φ.symm.injective e
    rw [← hPc] at e'
    exact (hs.toOpenPartialHomeomorph f).injOn hz.1 hz'.1 e'
  · have hfd := h1.continuousAt_fderiv (by norm_num)
    have hc2 : ContinuousAt (fun z => (Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z)) z0 :=
      continuousAt_const.clm_comp hfd
    exact continuous_abs.continuousAt.comp (ContinuousLinearMap.continuous_det.continuousAt.comp hc2)
  · rw [hd]
    exact Φ.coe_symm_comp_coe

open Classical in
theorem tupJac_of_pieces {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT
    (μinf : Measure (TupI X)) (νinf : Measure (HmI X)) fibInf (hP : PushHyp X u' ψ hT μinf νinf fibInf)
    (Ω : Set (HmI X)) (a : HmI X → MfI X) (hC : IsChart X u' hT Ω a) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) {η : Type} [Fintype η]
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ) (hν : νinf.map eH = ENNReal.ofReal cν • volume)
    (h1 : PolarChartContDiffAt X u' hT a κ eH) (h2 : PsiDet X u' hT a κ eH cν) : TupJac X u' hT μinf νinf a κ := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : BorelSpace (HmI X) := ⟨rfl⟩
  obtain ⟨Φ, Dv, hd, hDv, hvol, harith⟩ := h2
  set z0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
    ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) with hz0
  set f := PsiC X u' a κ eH with hf
  have hdetM : (matI X).det ≠ 0 := matNDH_holds X u' ψ hT μinf νinf fibInf hP
  have hsq : 0 < Real.sqrt |(matI X).det| := Real.sqrt_pos.2 (abs_pos.2 hdetM)
  have hcH : 0 < cν := by
    by_contra hne
    have h0 : cν = 0 := by
      rcases (not_lt.1 hne).lt_or_eq with h | h
      · exfalso
        have hz : ENNReal.ofReal cν = 0 := ENNReal.ofReal_of_nonpos h.le
        have := tVal_pos X u'
        rw [← harith] at this
        have hneg : Real.sqrt |(matI X).det| / (Dv * cν) < 0 := div_neg_of_pos_of_neg hsq (mul_neg_of_pos_of_neg hDv h)
        linarith
      · exact h
    have := tVal_pos X u'
    rw [← harith, h0, mul_zero, div_zero] at this
    exact lt_irrefl _ this

  have hvs : (volume : Measure (EuclideanSpace ℝ (KapI X))).map Φ.symm =
      (ENNReal.ofReal Dv)⁻¹ • volume := by
    have e1 : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) =
        ((volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map Φ).map Φ.symm := by
      rw [Measure.map_map Φ.symm.continuous.measurable Φ.continuous.measurable]
      have : (Φ.symm ∘ Φ : _ → _) = id := funext fun z => Φ.symm_apply_apply z
      rw [this, Measure.map_id]
    rw [hvol, Measure.map_smul] at e1
    have hD0 : ENNReal.ofReal Dv ≠ 0 := by simpa using hDv
    rw [e1, smul_smul, ENNReal.inv_mul_cancel hD0 ENNReal.ofReal_ne_top, one_smul]
  set eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) :=
    (tupCoord X).trans Φ.symm.toHomeomorph with heT
  have hμ : μinf.map eT = ENNReal.ofReal (Real.sqrt |(matI X).det| / Dv) • volume := by
    have e : (eT : TupI X → _) = Φ.symm ∘ tupCoord X := rfl
    rw [e, ← Measure.map_map Φ.symm.continuous.measurable (tupCoord X).continuous.measurable,
      densMu_holds X u' ψ hT μinf νinf fibInf hP, Measure.map_smul, hvs, smul_smul,
      ENNReal.ofReal_div_of_pos hDv, div_eq_mul_inv]

  obtain ⟨U, hUn, hder, hinj, hcont, hbase⟩ := loc_glue f z0 Φ h1 hd
  have hPsi : PsiM X u' a κ eT eH = Φ.symm ∘ f := rfl
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, hnear⟩ := nearFacts_of isOpen_units_tens X u' ψ hT μinf νinf fibInf hP Ω a hC
  refine ⟨η, inferInstance, eT, eH, Real.sqrt |(matI X).det| / Dv, cν,
    fun z => (Φ.symm : EuclideanSpace ℝ (KapI X) →L[ℝ] (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).comp (fderiv ℝ f z), U,
    div_pos hsq hDv, hcH, hμ, hν, hUn, ?_, ?_, hcont, ?_, ?_⟩
  · rw [hPsi]; exact hder
  · rw [hPsi]; exact hinj
  · filter_upwards [hΩ₁n] with T hT1
    exact ⟨(hnear T hT1).1, (hnear T hT1).2 _ (hC.2.2.2 T (hΩ₁ hT1))⟩
  · have hid : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).det = 1 := by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    simp only []
    rw [hbase, hid, abs_one, mul_one, div_div]
    exact harith

def TupPieces : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
    ∃ (η : Type) (_ : Fintype η) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ), νinf.map eH = ENNReal.ofReal cν • volume ∧
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → PolarChartContDiffAt X u' hT a (kap0 X hb c L) eH ∧ PsiDet X u' hT a (kap0 X hb c L) eH cν

theorem tupStd_of_pieces (h : TupPieces) : TupStd := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC, η, hη, eH, cν, hν, hJ⟩ := h X u' ψ hT μinf νinf fibInf hP
  refine ⟨Ω, a, hC, fun hb c S ι _ L hc hL => ?_⟩
  obtain ⟨h1, h2⟩ := hJ hb c S L hc hL
  exact tupJac_of_pieces X u' ψ hT μinf νinf fibInf hP Ω a hC _ eH cν hν h1 h2

end PI.AprimeInfW
