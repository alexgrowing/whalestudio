import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankPrincipalPolarisationSectionModuleLeOneStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneLeFinrankSecMStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem finrank_sections_principal_polarisation_eq_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))),
      Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1 :=
  fun K _ _ P => le_antisymm (GlobalTheory.T.finrank_principalPolarisation_sectionModule_le_one K P) (GlobalTheory.T.one_le_finrank_secM_one_of_isAlgClosed K P)

end GlobalTheory.AbLaw
