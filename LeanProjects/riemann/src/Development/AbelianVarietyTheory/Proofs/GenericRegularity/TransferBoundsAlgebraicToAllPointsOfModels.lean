import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsEveryFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineChartsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValuesStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem transfer_of_models : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → (∀ la, ModelAt Xo c la) → (∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U) ∧ ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro hS E _ _ _ H Dw l Xo c hEv hInt hM
  have hN := fun la => GlobalTheory.T.exists_normalCharts_everyFinitePlace hS E H Dw l Xo c hEv hInt la (hM la)
  refine ⟨GlobalTheory.Reg.Transfer.transferLaw_of_normalCharts E H Dw l Xo c hN, fun C hC => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.T.integrality_trivialValuations_of_normalAffineCharts E H Dw l Xo c hN C hC).1
  · exact combined_bound_at_trivial_valuations_of_charts E H Dw l Xo c hN
      (fun la a n m ws hws hv => GlobalTheory.T.noCommonZero_of_exists_finite_value hS E H Dw l Xo c hEv la (hM la) a n m ws hws hv) C hC

end GlobalTheory.Reg
