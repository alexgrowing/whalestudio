import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmGoodModelOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenusOneFormalIsoOfUnramifiedGoodReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TorsionTaylorAlgebraicLatticeExistsOfCm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntInertOfComplexMultiplicationCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypothesesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd)
      (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro hA Bd Q Lk ker hQ hE
  have h2 : Formalism.L2.Th1.CM.CM2 := GlobalTheory.Corev.CmTwoClosing.cmGoodModel_of_globalArtinReciprocity hA
  obtain ⟨hT, hG, hC⟩ := GlobalTheory.CurveThetaInert.torsionTaylorAlgebraic_latticeExists_of_cm h2
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses hT hG hC (GlobalTheory.intInert_of_complexMultiplication_condition h2) (GlobalTheory.TwV.Lt.inert_theta_admissibility_of_complex_multiplication h2)
    (GlobalTheory.TwV.Lt.exists_genusOne_formal_iso_of_unramified_good_reduction h2) Q Lk ker hQ hE

end GlobalTheory.Svd
