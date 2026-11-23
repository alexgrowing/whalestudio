import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.LocTateInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)

theorem finite_FE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

attribute [local instance] finite_FE

def basisEv : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

theorem isModuleTopology_Ev : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

def coordEv : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
  haveI := isModuleTopology_Ev (E := E) v
  { (basisEv v).equivFun.toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.symm.toLinearMap }

theorem isTopologicalRing_Ev : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens

theorem t2Space_Fv_tensor : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

theorem locallyCompactSpace_Ev : LocallyCompactSpace (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

theorem secondCountable_Ev : SecondCountableTopology (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isEmbedding.secondCountableTopology

theorem isOpenUnits_Ev : IsOpenUnits (Fv F v ⊗[F] E) :=
  haveI := isModuleTopology_Ev (E := E) v
  haveI := isTopologicalRing_Ev (E := E) v
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (basisEv v)

attribute [local instance] isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

theorem distribHaarChar_Ev (u : (Fv F v ⊗[F] E)ˣ) :
    distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
  borelize (Fv F v ⊗[F] E)
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set b := basisEv (E := E) v
  set M := Algebra.leftMulMatrix b (u : Fv F v ⊗[F] E) with hMdef
  have hdet : M.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det b _).symm
  have hM : IsUnit M.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
  have hN0 : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hM).ne_zero
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
  have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (coordEv (E := E) v).symm (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : (((coordEv (E := E) v).symm.symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (coordEv (E := E) v).symm) =
      GlobalTheory.ModuNorm.mulUnitCE u := by
    ext x
    show b.equivFun.symm (Matrix.mulVec M (b.equivFun x)) = (u : Fv F v ⊗[F] E) * x
    rw [show Matrix.mulVec M (b.equivFun x) = b.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr b _ x,
      LinearEquiv.symm_apply_apply]
  rw [hext] at ht
  rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu,
    dif_pos (hdet ▸ hM)]
  convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN0 using 2
  exact Units.ext rfl

end GlobalTheory.LocTateInt

namespace GlobalTheory.LocTateInt

open scoped Pointwise

attribute [local instance] finite_FE isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

theorem integrable_indicator_absE_pow : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∀ (C : Set (Fv F v ⊗[F] E)), IsCompact C → ∀ z : ℕ, 1 ≤ z →
      Integrable (fun l : idelesAt E (evFin F v) =>
        C.indicator (fun _ => ((GlobalTheory.Doubling.absE F E l.1 : ℝ)) ^ z) (compFin F E v l.1)) μ := by
  intro F E _ _ _ _ _ v μ hμ C hC z hz
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  borelize (Fv F v ⊗[F] E)
  set φ := idelesAtEquiv E v with hφ
  let j : idelesAt E (evFin F v) → Fv F v ⊗[F] E := fun l => ((φ l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)
  have hoe : Topology.IsOpenEmbedding j :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).comp φ.toHomeomorph.isOpenEmbedding
  have hme : MeasurableEmbedding j := hoe.measurableEmbedding
  set lam : Measure (Fv F v ⊗[F] E) := Measure.addHaar with hlam
  set ν : Measure (idelesAt E (evFin F v)) := lam.comap j with hν
  have hνa : ∀ s, ν s = lam (j '' s) := fun s => hme.comap_apply lam s
  have hne : ∀ x : (Fv F v ⊗[F] E)ˣ, GlobalTheory.Doubling.absEv F E v x ≠ 0 := fun x h => by
    have e := congrArg (GlobalTheory.Doubling.absEv F E v) (mul_inv_cancel x)
    rw [map_mul, map_one, h, zero_mul] at e
    exact zero_ne_one e
  set f : idelesAt E (evFin F v) → ℝ≥0 := fun l => (GlobalTheory.Doubling.absEv F E v (φ l))⁻¹ with hf
  have hfc : Continuous f :=
    ((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous).inv₀ fun l => hne _
  have hfm : ∀ x y, f (x * y) = f x * f y := fun x y => by
    simp only [hf, map_mul, mul_inv]
  have hf1 : ∀ a, f a⁻¹ * f a = 1 := fun a => by
    rw [← hfm, inv_mul_cancel]
    simp [hf]
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := lam.finiteAt_nhds (j x)
    refine ⟨j ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero lam (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => ENNReal.coe_ne_zero.2 (inv_ne_zero (hne _))
  have hinv : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : idelesAt E (evFin F v) => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : idelesAt E (evFin F v) => a * x) ν = (f a : ℝ≥0∞) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul]
      have e : j '' ((fun x => a * x) ⁻¹' s) = (φ a)⁻¹ • (j '' s) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨j (a * x), ⟨a * x, hx, rfl⟩, ?_⟩
          simp [j, Units.smul_def, map_mul]
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨a⁻¹ * x, by simpa using hx, ?_⟩
          simp [j, Units.smul_def, map_mul, map_inv]
      rw [e, ← distribHaarChar_mul lam (φ a)⁻¹ (j '' s), map_inv, distribHaarChar_Ev]
      rfl
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x, (f x : ℝ≥0∞) = (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) := fun x => by
      rw [← ENNReal.coe_mul, hfm, ← mul_assoc, hf1, one_mul]
    have h2 : (f a⁻¹ : ℝ≥0∞) * (f a : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_mul, hf1, ENNReal.coe_one]
    calc ∫⁻ x in (fun x => a * x) ⁻¹' s, (f x : ℝ≥0∞) ∂ν
        = ∫⁻ x in (fun x => a * x) ⁻¹' s, (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) ∂ν := lintegral_congr h1
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in (fun x => a * x) ⁻¹' s, (f (a * x) : ℝ≥0∞) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in s, (f x : ℝ≥0∞) ∂(Measure.map (fun x => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2, one_mul]
  set ρ := ν.withDensity fun x => (f x : ℝ≥0∞) with hρ
  haveI : ρ.IsHaarMeasure := ⟨⟩
  obtain ⟨c, -, hc⟩ := haar_idelesAt_eq_smul μ ρ
  rw [hc]
  refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
  set g : idelesAt E (evFin F v) → ℝ := fun l => ((GlobalTheory.Doubling.absEv F E v (φ l) : ℝ)) ^ z with hg
  have hfun : (fun l : idelesAt E (evFin F v) =>
      C.indicator (fun _ => ((GlobalTheory.Doubling.absE F E l.1 : ℝ)) ^ z) (compFin F E v l.1)) = (j ⁻¹' C).indicator g := by
    funext l
    by_cases h : j l ∈ C
    · rw [Set.indicator_of_mem (show compFin F E v l.1 ∈ C from h), Set.indicator_of_mem (show l ∈ j ⁻¹' C from h),
        absE_of_mem l.2]
      rfl
    · rw [Set.indicator_of_notMem (show compFin F E v l.1 ∉ C from h),
        Set.indicator_of_notMem (show l ∉ j ⁻¹' C from h)]
  rw [hfun]
  have hCm : MeasurableSet (j ⁻¹' C) := hme.measurable hC.isClosed.measurableSet
  have hgc : Continuous g :=
    (NNReal.continuous_coe.comp ((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous)).pow z
  have hhm : Measurable ((j ⁻¹' C).indicator g) := hgc.measurable.indicator hCm
  refine ⟨hhm.aestronglyMeasurable, ?_⟩
  have hNc : Continuous fun x : Fv F v ⊗[F] E => ‖Algebra.norm (Fv F v) x‖₊ :=
    (GlobalTheory.Doubling.continuous_norm_tens (F := F) (E := E) (R := Fv F v)).nnnorm
  obtain ⟨M, hM⟩ := (hC.image hNc).bddAbove
  have hb : ∀ l, (f l : ℝ≥0∞) * ‖(j ⁻¹' C).indicator g l‖ₑ ≤ (j ⁻¹' C).indicator (fun _ => ((M ^ (z - 1) : ℝ≥0) : ℝ≥0∞)) l := by
    intro l
    by_cases h : l ∈ j ⁻¹' C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      set a := GlobalTheory.Doubling.absEv F E v (φ l) with ha
      have ha0 : a ≠ 0 := hne _
      have haM : a ≤ M := hM ⟨j l, h, rfl⟩
      have e1 : ‖g l‖ₑ = ((a ^ z : ℝ≥0) : ℝ≥0∞) := by simp [hg, ← ha]
      rw [e1, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      have e2 : f l * a ^ z = a ^ (z - 1) := by
        rw [show f l = a⁻¹ from rfl, ← mul_pow_sub_one (show z ≠ 0 by omega) a, inv_mul_cancel_left₀ ha0]
      rw [e2]
      exact pow_le_pow_left₀ zero_le haM _
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  show ∫⁻ l, ‖(j ⁻¹' C).indicator g l‖ₑ ∂ρ < ⊤
  rw [hρ, lintegral_withDensity_eq_lintegral_mul _ hfc.measurable.coe_nnreal_ennreal hhm.enorm]
  calc ∫⁻ l, ((fun x => (f x : ℝ≥0∞)) * fun l => ‖(j ⁻¹' C).indicator g l‖ₑ) l ∂ν
      ≤ ∫⁻ l, (j ⁻¹' C).indicator (fun _ => ((M ^ (z - 1) : ℝ≥0) : ℝ≥0∞)) l ∂ν := lintegral_mono hb
    _ = ((M ^ (z - 1) : ℝ≥0) : ℝ≥0∞) * ν (j ⁻¹' C) := lintegral_indicator_const hCm _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
      rw [hνa]
      exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hC.measure_lt_top

end GlobalTheory.LocTateInt
