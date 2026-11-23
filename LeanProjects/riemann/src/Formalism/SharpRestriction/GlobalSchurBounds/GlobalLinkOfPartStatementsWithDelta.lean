import Formalism.SharpRestriction.GlobalSchurBounds.LossesSmallShares
import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

theorem global_link_of_part_statements_with_delta {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 C3 crystallineComparison C22 : ℝ)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 1 ≤ C0)
    (s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))
    (s22 : TaylorLogMetric.StatementFamilyConstant Fm C22) (s23 : flipTwoThree.KudlaFamilyStatement Fm) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) (s10 : product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison)
    (hF3 : StandardLattice.FamilyTheoremThreeAdmitted Fm)
    (tVol : StandardLattice.TiesF Fm)
    (tOm : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ))
    (tFree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (tTh : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22)
    (t7 : flipTwoThree.admF7 Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (t10 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_pk Fm Cabs CH C0 C3 crystallineComparison C22 hCabs hCH hC0 s59 s22 s23 s24 s10
    (Formalism.L2.GlobalTheoryTheory.Loss7.stLoss7 eps Fm) hF3 tVol tOm tFree tTh t7 tCV t10

end Formalism.MainNotions

end
