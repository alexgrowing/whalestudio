import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelCov

section Gen

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR

theorem chi_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  let Mi : Matrix κ κ (Ainf F) := (fstA F).toRingHom.mapMatrix M
  let Mf : Matrix κ κ (Af F) := (sndA F).toRingHom.mapMatrix M
  have hi : Mi.det = fstA F M.det := (RingHom.map_det _ _).symm
  have hf : Mf.det = sndA F M.det := (RingHom.map_det _ _).symm
  have hMi : IsUnit Mi.det := hi ▸ hM.map (fstA F)
  have hMf : IsUnit Mf.det := hf ▸ hM.map (sndA F)
  let j : (κ → Ainf F) × (κ → Af F) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have s1 : addEquivAddHaarChar (mulVecCE M hM) =
      addEquivAddHaarChar (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) :=
    GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ j hj (mulVecCE M hM) (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) fun p => by
      funext i
      show (M *ᵥ j p) i = ((Mi *ᵥ p.1) i, (Mf *ᵥ p.2) i)
      have e1 : fstA F ((M *ᵥ j p) i) = (Mi *ᵥ p.1) i := by
        rw [show (fstA F) ((M *ᵥ j p) i) = (fstA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      have e2 : sndA F ((M *ᵥ j p) i) = (Mf *ᵥ p.2) i := by
        rw [show (sndA F) ((M *ᵥ j p) i) = (sndA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      rw [← e1, ← e2]
      rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  have s2 : addEquivAddHaarChar (mulVecCE Mi hMi) = modu (Ainf F) Mi.det :=
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F) inferInstance inferInstance κ Mi hMi
  rw [s1, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, s2, chi_Af F Mf hMf, hi, hf]

theorem addEquivAddHaarChar_mulVecCE_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  let N : Matrix Unit Unit (AF F) := fun _ _ => M.det
  have hdet : N.det = M.det := Matrix.det_unique N
  have hN : IsUnit N.det := hdet ▸ hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)
  have hext : ((GlobalTheory.ModuNorm.evalUnitCE (AF F)).symm.trans (mulVecCE N hN)).trans (GlobalTheory.ModuNorm.evalUnitCE (AF F)) =
      GlobalTheory.ModuNorm.mulUnitCE hM.unit := by
    ext x
    show (N *ᵥ fun _ => x) () = M.det * x
    simp [Matrix.mulVec, dotProduct, N]
  rw [hext] at htr
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, htr]
  apply NNReal.coe_injective
  rw [chi_adele, chi_adele, hdet]

end Gen

end GlobalTheory.SiegelCov

namespace GlobalTheory.SiegelCov

section Coord

open Matrix GlobalTheory.ModuLR

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

def vecCoord : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1) p.2
  invFun x i := (tensBasis F E).equivFun.symm fun k => x (i, k)
  left_inv u := by
    funext i
    exact (tensBasis F E).equivFun.symm_apply_apply (u i)
  right_inv x := by
    funext p
    obtain ⟨i, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, k)) k = x (i, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_vecCoord : Continuous (vecCoord F E n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2).comp (hb.comp (continuous_apply p.1))

theorem continuous_vecCoord_symm : Continuous (vecCoord F E n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => hb.comp (continuous_pi fun k => continuous_apply (i, k))

def vecCoordCE : (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F) :=
  { (vecCoord F E n).toAddEquiv with
    continuous_toFun := continuous_vecCoord F E n
    continuous_invFun := continuous_vecCoord_symm F E n }

end Coord

end GlobalTheory.SiegelCov

open GlobalTheory.GaugeEx in

theorem GlobalTheory.SiegelCov.integral_mulVec_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ (t : GL (Fin n) (AE F E)) (f : (Fin n → AE F E) → ℂ),
      (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) →
      (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, f (((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ y) ∂μ) =
        (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) : ℂ) *
          (letI : MeasurableSpace (Fin n → AE F E) := borel _; ∫ y, f y ∂μ) := by
  intro F E _ _ _ _ _ n μ hμ t f _
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  let Φ := GlobalTheory.SiegelCov.vecCoordCE F E n
  haveI : LocallyCompactSpace (Fin n → AE F E) := Φ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin n → AE F E) := Φ.toHomeomorph.isInducing.secondCountableTopology
  haveI : T2Space (Fin n → AE F E) := Φ.toHomeomorph.isEmbedding.t2Space
  haveI : μ.IsAddHaarMeasure := hμ
  set T : Matrix (Fin n) (Fin n) (AE F E) := ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hTdef
  have hT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 (t⁻¹).isUnit
  set L := GlobalTheory.ModuLR.mulVecCE T hT with hL
  set Λ := LinearMap.toMatrix' ((GlobalTheory.SiegelCov.vecCoord F E n).toLinearMap ∘ₗ
    (Matrix.toLin' T).restrictScalars (AF F) ∘ₗ (GlobalTheory.SiegelCov.vecCoord F E n).symm.toLinearMap) with hΛdef
  have hdet : Λ.det = Algebra.norm (AF F) T.det := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have hΛ : IsUnit Λ.det := hdet ▸ hT.map (Algebra.norm (AF F))
  have hc : GlobalTheory.ModuLR.mulVecCE Λ hΛ = (Φ.symm.trans L).trans Φ := by
    ext x
    rw [GlobalTheory.ModuLR.mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  have hχ : addEquivAddHaarChar L = distribHaarChar (AF F) hΛ.unit := by
    rw [← GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele, hc, GlobalTheory.ModuLR.addEquivAddHaarChar_transport]
  have hu : hΛ.unit = (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))⁻¹ := by
    ext
    rw [IsUnit.unit_spec, hdet, hTdef]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have key := addEquivAddHaarChar_smul_map μ L
  set c := addEquivAddHaarChar L with hcdef
  have hc0 : c ≠ 0 := (addEquivAddHaarChar_pos L).ne'
  have hmap : μ.map L = c⁻¹ • μ := by
    calc μ.map L = (c⁻¹ * c) • μ.map L := by rw [inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ y, f (T *ᵥ y) ∂μ = ∫ y, f y ∂(μ.map L) :=
    (integral_map_equiv L.toHomeomorph.toMeasurableEquiv f).symm
  have hmodu : ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
      (Matrix.GeneralLinearGroup.det t)) : ℝ≥0) = c⁻¹ := by
    rw [hχ, hu, map_inv, inv_inv]
    rfl
  show ∫ y, f (T *ᵥ y) ∂μ = _
  rw [hint, hmap, integral_smul_nnreal_measure, hmodu, NNReal.smul_def, Complex.real_smul]
