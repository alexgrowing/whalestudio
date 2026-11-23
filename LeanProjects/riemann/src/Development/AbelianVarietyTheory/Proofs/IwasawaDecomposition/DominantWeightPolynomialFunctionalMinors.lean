import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BideterminantFunctionsOfShape
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionalFrameMinorPolynomialsEqMinorProdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightPolynomialFramesMemSpanBideterminantProducStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdBideterminantsEqColumnChoiceMinorProductStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CanonicalSurjection

theorem canOnto_all : ∀ (D : D7) (Pl : Examples₂.EntPl D), CanOnto Pl := by
  intro D Pl w N nu ν hfit Q hQ M
  haveI : Infinite D.what₂.LL := Infinite.of_injective (Nat.cast : ℕ → D.what₂.LL) Nat.cast_injective
  have h := GlobalTheory.T.weightPolynomial_frames_mem_span_bideterminantProducts D.what₂.LL (Cw D w) (Pl.iL w) D.what₂.Tau N ν M Q hQ
  have e : atBas Pl w M Q = fun y : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w) =>
      MvPolynomial.eval (fun k : D.what₂.Tau × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2)
        (MvPolynomial.map (Pl.iL w) Q) := rfl
  rw [e]
  refine Submodule.span_le.2 ?_ h
  rintro F ⟨g, hg, rfl⟩
  obtain ⟨J, hJ⟩ := GlobalTheory.T.prod_bideterminants_eq_columnChoice_minorProduct D (Cw D w) N nu ν hfit g hg
  obtain ⟨ph, hph⟩ := GlobalTheory.T.exists_functional_frameMinorPolynomials_eq_minorProduct D (Cw D w) N nu J
  refine ⟨ph, ?_⟩
  funext y
  rw [hJ y]
  exact hph _

end GlobalTheory.Mem.CanonicalSurjection
