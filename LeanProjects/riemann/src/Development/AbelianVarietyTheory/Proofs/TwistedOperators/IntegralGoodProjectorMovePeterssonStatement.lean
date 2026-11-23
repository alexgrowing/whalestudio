import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralGoodProjectorMovePetersson
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_goodProjector_move_petersson : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (Φ : GA D (Wc D i) → ℂ), (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) → (∀ y : (R.HW i σ).H, IntegrableOn (fun g => star (Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g) (R.fdW i) (R.νW i)) → ∀ y : (R.HW i σ).H, ∫ g in R.fdW i, star (R.eWf i σ Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g ∂(R.νW i) = ∫ g in R.fdW i, star (Φ g) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) := by
  first | exact @GlobalTheory.EwfMove.integral_eWf_move | exact GlobalTheory.EwfMove.integral_eWf_move | (intros; apply GlobalTheory.EwfMove.integral_eWf_move <;> assumption)
