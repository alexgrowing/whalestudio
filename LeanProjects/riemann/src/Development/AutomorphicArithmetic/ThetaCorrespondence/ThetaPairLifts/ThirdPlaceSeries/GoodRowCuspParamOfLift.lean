import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrivialPartInBaseChange
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParamOfLiftStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.ParAsm
theorem goodRowCuspParam_of_lift_alt : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D →
    (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) →
    GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  intro D Rw hL h45 hEFK hCM hdef hLift hLoc j hj1 hj2 σ hiso hgood
  obtain ⟨π, μ, hπ⟩ := hLift j hj1 hj2 σ hiso
  obtain ⟨Pa, hPa⟩ := h45 hEFK hCM j hj1 hj2 (one_le_nV D) (hdef j hj1 hj2) π hπ.sph
  have hmu := _root_.GlobalTheory.T.trivial_piece_mem_base_change D Rw hL j σ π μ Pa hπ (hLoc σ) hPa
  exact _root_.GlobalTheory.T.exists_isCuspParam_of_bc_good_index D Rw hL j σ π μ Pa hπ (hLoc σ) hPa hmu hgood
end GlobalTheory.ParAsm
end
