import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftCoefCont

theorem continuous_l2_weil_action_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hc Q₁ Q₂
  obtain ⟨-, -, -, -, -, hom, -, -, hpt, -, -⟩ := h
  have e : ∀ g : GA D (Wc D i), l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) =
      GlobalTheory.RawLift.thetaIP μ 𝓧 (ptAt R i σ BW f Q₂) (ω (1, g) (ptAt R i σ BW f Q₁)) := fun g => by
    rw [← GlobalTheory.RawLift.FockCoef.thetaInner_star, GlobalTheory.RawLift.GoodModulus.thetaInner_eq_star_l2, star_star]
  simp only [e]
  exact GlobalTheory.RawLift.FockCoef.continuous_coef hom hc (hpt Q₂) (hpt Q₁)

end GlobalTheory.LiftCoefCont

end
