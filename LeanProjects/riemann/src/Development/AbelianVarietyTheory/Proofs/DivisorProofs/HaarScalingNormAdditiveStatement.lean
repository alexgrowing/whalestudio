import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

private theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (AE F E)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

theorem _root_.GlobalTheory.T.haar_scaling_norm_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ [MeasurableSpace (AF F)] [BorelSpace (AF F)] (ν : Measure (AF F)), ν.IsAddHaarMeasure →
  ∀ t : (AE F E)ˣ, ν.map (fun a => Algebra.norm (AF F) (t : AE F E) * a) = ((absE F E t : ENNReal))⁻¹ • ν := by
  intro F E _ _ _ _ _ σ _ m hm ν hν t
  have hb : @BorelSpace (AF F) _ (GroundTheory.Global.measurableSpace_adeleRing F) := GroundTheory.Global.borelSpace_adeleRing F
  obtain rfl : m = GroundTheory.Global.measurableSpace_adeleRing F :=
    (@BorelSpace.measurable_eq _ _ m hm).trans (@BorelSpace.measurable_eq _ _ _ hb).symm
  letI : MeasurableSpace (AF F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hμ := Measure.isAddLeftInvariant_eq_smul ν (GroundTheory.Global.adeleMeasure F)
  have hs := GroundTheory.Global.map_smul_adeleMeasure (K := F) (Units.map (Algebra.norm (AF F)) t)
  rw [ideleModule_norm] at hs
  have hpos : absE F E t ≠ 0 := ((Group.isUnit t).map (absE F E)).ne_zero
  have hc : ENNReal.ofReal ((absE F E t : ℝ))⁻¹ = ((absE F E t : ENNReal))⁻¹ := by
    rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv hpos]
  rw [hc] at hs
  have hs' : (GroundTheory.Global.adeleMeasure F).map (fun a => Algebra.norm (AF F) (t : AE F E) * a) =
      ((absE F E t : ENNReal))⁻¹ • GroundTheory.Global.adeleMeasure F := hs
  generalize Measure.addHaarScalarFactor ν (GroundTheory.Global.adeleMeasure F) = c at hμ
  rw [hμ, Measure.map_smul, hs', smul_comm]
