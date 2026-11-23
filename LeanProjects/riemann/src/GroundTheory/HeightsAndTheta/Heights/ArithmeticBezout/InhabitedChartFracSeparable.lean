import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealBelow
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartKernel
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncDomain
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial LineChowForm SectionLine

noncomputable section

namespace ChartFracSeparableInhabited

theorem chartLocDomain : ChartLocDomain.Statement :=
  ChartLocDomain.proof (IncIdealBelow.proof ChowFormMultiHomog.full) ChartIncDomain.proof
    (ChartKernel.proof IncidenceGeneric.full ChartIncDomain.proof)

theorem line_domain (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    IsDomain (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) ∧
      Function.Injective (algebraMap (Localization.AtPrime p)
        (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) := by
  obtain ⟨hdom, hinj, -⟩ := chartLocDomain F 2 1 ⊥ D2 (coeffX1 F) p isProjPrime_line isChowForm_line
    (linearFormX1_ne_zero F)
  exact ⟨hdom, hinj⟩

scoped instance line_isDomain (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    IsDomain (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) :=
  (line_domain F p).1

scoped instance line_isTorsionFree (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (line_domain F p).2

set_option synthInstance.maxHeartbeats 400000 in

scoped instance line_faithfulSMul (F : Type) [Field F] (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    FaithfulSMul (Localization.AtPrime p) (FractionRing (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (Localization.AtPrime p)
    (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)]
  rw [RingHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (line_domain F p).2

end ChartFracSeparableInhabited

open ChartFracSeparableInhabited in

theorem ChartFracSeparable.hypotheses_inhabited_full (F : Type) [Field F] [PerfectField F]
    (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) F)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) F)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) F) ∧
      linForm (coeffX1 F) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) F)) ∧
      IsDomain (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p) ∧
      Function.Injective (algebraMap (Localization.AtPrime p)
        (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) :=
  ⟨isProjPrime_line, isChowForm_line, linearFormX1_ne_zero F, line_domain F p⟩

set_option synthInstance.maxHeartbeats 400000 in
open ChartFracSeparableInhabited in

theorem ChartFracSeparable.applies_line (h : ChartFracSeparable.Statement) (F : Type) [Field F] [PerfectField F]
    (p : Ideal (MvPolynomial (Fin 1 × Fin 2) F)) [p.IsPrime] :
    letI := FractionRing.liftAlgebra (Localization.AtPrime p)
      (FractionRing (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p))
    Algebra.IsSeparable (FractionRing (Localization.AtPrime p))
      (FractionRing (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) := by
  let _ := FractionRing.liftAlgebra (Localization.AtPrime p)
    (FractionRing (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p))
  have hs : Algebra.IsSeparable (FractionRing (Localization.AtPrime p))
      (FractionRing (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) F)) (coeffX1 F) 1 p)) :=
    @h F _ _ 2 1 ⊥ D2 (coeffX1 F) p _ _ _ _ _ OreLocalization.instAlgebra Localization.isLocalization _
      Localization.isLocalization _ _ (FractionRing.isScalarTower_liftAlgebra _ _) _ isProjPrime_line
      isChowForm_line (linearFormX1_ne_zero F)
  exact hs

theorem ChartFracSeparable.hypotheses_inhabited_zmod2_full :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) (ZMod 2))) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) (ZMod 2))) (1 + 1)
        (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) (ZMod 2)) ∧
      linForm (coeffX1 (ZMod 2)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) (ZMod 2))) ∧
      IsDomain (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) (ZMod 2))) (coeffX1 (ZMod 2)) 1 ⊥) ∧
      Function.Injective (algebraMap (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin 1 × Fin 2) (ZMod 2))))
        (ChartLoc (⊥ : Ideal (MvPolynomial (Fin 2) (ZMod 2))) (coeffX1 (ZMod 2)) 1 ⊥)) :=
  ChartFracSeparable.hypotheses_inhabited_full (ZMod 2) ⊥

end

end GroundTheory.Heights₂.Heights
