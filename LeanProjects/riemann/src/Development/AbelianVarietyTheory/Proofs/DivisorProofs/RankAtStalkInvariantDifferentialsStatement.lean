import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtStalkInvariantDifferentials
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_at_stalk_invariant_differentials : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] (d : ℕ), GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega A) d → ∀ p : PrimeSpectrum O, Module.rankAtStalk (R := O) (GlobalTheory.SqZeroPt.Wmod A) p = d := by
  first | exact @GlobalTheory.WmodRank.rankAtStalk_wmod | exact GlobalTheory.WmodRank.rankAtStalk_wmod | (intros; apply GlobalTheory.WmodRank.rankAtStalk_wmod <;> assumption)
