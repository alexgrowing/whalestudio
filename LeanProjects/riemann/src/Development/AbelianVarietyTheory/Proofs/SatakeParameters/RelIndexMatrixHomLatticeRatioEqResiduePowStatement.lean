import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePow
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p n' : ℕ) (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {k k' : ℕ} (a₀ a₁ : Matrix (Fin k) (Fin k) Qq) (b₀ b₁ : Matrix (Fin k') (Fin k') Qq) (ha₀ : IsUnit a₀.det) (ha₁ : IsUnit a₁.det) (hb₀ : IsUnit b₀.det) (hb₁ : IsUnit b₁.det), (((homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup.relIndex (homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup : ℕ) : ℝ) / (((homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup.relIndex (homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k : ℤ) * (ordP W p b₀.det - ordP W p b₁.det) - (k' : ℤ) * (ordP W p a₀.det - ordP W p a₁.det))) := by
  first | exact @GlobalTheory.HomLatIndex.relIndex_homLat_ratio | exact GlobalTheory.HomLatIndex.relIndex_homLat_ratio | (intros; apply GlobalTheory.HomLatIndex.relIndex_homLat_ratio <;> assumption)
