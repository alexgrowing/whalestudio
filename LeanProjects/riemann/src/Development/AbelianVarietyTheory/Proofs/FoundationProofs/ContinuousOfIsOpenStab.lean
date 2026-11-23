import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.NormNatCastLtOne
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V
open scoped Matrix TensorProduct

namespace GlobalTheory.SlTwoCusp

open Topology

theorem continuous_pInf' (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  exact hc.comp continuous_fst

theorem continuous_of_isOpen_stab : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a),
    IsOpen {k | TR.finRep F a k φ = φ} → Continuous φ.1 := by
  intro F _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA F a => g⁻¹ * x := continuous_const.mul continuous_id
  have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F a → GL (Fin a) (TR.Rinf F)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf' F))
  have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F a → GL (Fin a) (Af F)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  have h1 : Continuous fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp (hI.comp hm)
  have h2 : ContinuousAt (fun x : GA F a => TR.chart φ.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
      (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA F a | TR.finRep F a (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage (hFn.comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [TR.chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * TR.infGL F a _ * finGL F a _) = _
  rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]

open MeasureTheory Topology

end GlobalTheory.SlTwoCusp
