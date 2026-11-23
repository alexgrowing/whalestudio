import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRank
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_subbundle_rank : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (i : Fin (N + 1)), VB.IsVB (F ι N τ i) i ∧ VB.IsSubbundle (incl ι N τ i) := by
  first | exact @GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl | exact GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl | (intros; apply GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl <;> assumption)
