import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPieceFinrankLeH0
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_piece_finrank_le_h0 : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ m : ℕ, Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  first | exact @GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections | exact GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections | (intros; apply GlobalTheory.Adelic.LinSys.finrank_quotient_piece_le_sections <;> assumption)
