import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialPartInBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRowStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ParAsm

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.nV, Ranks.r] at *
  omega

theorem goodRowCuspParam_of_lift : ∀ (D : D7) (Rw : RowSide D), ParLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D →
    (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) →
    GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  intro D Rw hL h45 hEFK hCM hdef hLift hLoc j hj1 hj2 σ hiso hgood
  obtain ⟨π, μ, hπ⟩ := hLift j hj1 hj2 σ hiso
  obtain ⟨Pa, hPa⟩ := h45 hEFK hCM j hj1 hj2 (one_le_nV D) (hdef j hj1 hj2) π hπ.sph
  have hmu := GlobalTheory.T.trivial_part_in_base_change D Rw hL j σ π μ Pa hπ (hLoc σ) hPa
  exact GlobalTheory.T.exists_cusp_param_good_row D Rw hL j σ π μ Pa hπ (hLoc σ) hPa hmu hgood

end GlobalTheory.ParAsm
