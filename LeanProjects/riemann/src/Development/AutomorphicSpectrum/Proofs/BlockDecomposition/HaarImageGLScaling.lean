import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.SwmConeHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.LocalModule

open IsDedekindDomain NumberField

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Rv" => HeckeCharacterZeroLocus.SiegelWeilU.Fv F v
local notation "Av" => (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)

def mulVecA (g : GL (Fin n) Av) : (Fin n → Av) ≃ₗ[Av] (Fin n → Av) :=
  LinearEquiv.ofLinear (Matrix.toLin' g.1) (Matrix.toLin' (g⁻¹).1)
    (by rw [← Matrix.toLin'_mul]; simp)
    (by rw [← Matrix.toLin'_mul]; simp)

theorem absF_eq_nnnorm (x : Rv) : GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys.absF x = ‖x‖₊ := by
  by_cases hx : x = 0
  · simp [GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys.absF, hx]
  · have hu : IsUnit x := isUnit_iff_ne_zero.2 hx
    have h := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at h
    simp only [GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys.absF, dif_neg hx]
    apply NNReal.coe_injective
    rw [coe_nnnorm, ← h]
    congr 2
    exact Units.ext rfl

theorem det_mulVecA (g : GL (Fin n) Av) :
    LinearMap.det (((mulVecA v g).restrictScalars Rv : (Fin n → Av) ≃ₗ[Rv] (Fin n → Av)) :
      (Fin n → Av) →ₗ[Rv] (Fin n → Av)) = Algebra.norm Rv (g.1.det) := by
  have h := LinearMap.det_restrictScalars (R := Rv) (S := Av)
    (f := ((mulVecA v g : (Fin n → Av) ≃ₗ[Av] (Fin n → Av)) : (Fin n → Av) →ₗ[Av] (Fin n → Av)))
  have e : ((mulVecA v g : (Fin n → Av) ≃ₗ[Av] (Fin n → Av)) : (Fin n → Av) →ₗ[Av] (Fin n → Av)) =
      Matrix.toLin' g.1 := rfl
  rw [e, LinearMap.det_toLin'] at h
  exact h

theorem haar_mulVec_image (lam : Measure (Fin n → Av)) [lam.IsAddHaarMeasure] (g : GL (Fin n) Av)
    (S : Set (Fin n → Av)) :
    lam ((fun x => g.1.mulVec x) '' S) =
      (absEv F E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S := by
  haveI : IsModuleTopology Rv Av := ⟨rfl⟩
  haveI : SecondCountableTopology Rv :=
    GroundTheory.Heights₂.Theta.SwmCone.secondCountableTopology_adicCompletion v
  have hd := GroundTheory.Heights₂.Theta.SwmCone.not_discreteTopology_adicCompletion (K := F) v
  let L : (Fin n → Av) ≃ₗ[Rv] (Fin n → Av) := (mulVecA v g).restrictScalars Rv
  let H : (Fin n → Av) ≃ₜ+ (Fin n → Av) :=
    { L.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }
  have hc := GroundTheory.Heights₂.Theta.WmSysEquiv.addEquivAddHaarChar_eq_absF_det hd L H (fun _ => rfl)
  haveI : T2Space (Fin n → Av) := inferInstance
  haveI : SecondCountableTopology (Fin n → Av) := inferInstance
  haveI : LocallyCompactSpace (Fin n → Av) := inferInstance
  haveI : SigmaCompactSpace (Fin n → Av) := inferInstance
  haveI : TopologicalSpace.PseudoMetrizableSpace (Fin n → Av) := by
    haveI : T3Space (Fin n → Av) := inferInstance
    infer_instance
  haveI : lam.Regular := inferInstance
  have h := addEquivAddHaarChar_smul_preimage lam (X := H '' S) H
  rw [Set.preimage_image_eq S H.injective] at h
  change lam (H '' S) = _
  rw [← h, ENNReal.smul_def, smul_eq_mul, hc, det_mulVecA, absF_eq_nnnorm]
  rfl

end Gen

end GlobalTheory.CompanionTheory.LocalModule

theorem GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image_host : ∀ (D : D7) (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → ∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S := by
  intro D n v lam hlam g S
  exact GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image v lam g S
