import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsionStatement

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (y : Fin 2 → ZMod N), y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (IsAlgebraic ℚ) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL z hz κ y hy α
  have hy' : vmul y α ≠ 0 := fun h => hy (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.2.1 y α).1 h)
  exact GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients hE F hF s N _ hs (Nat.pos_of_ne_zero (NeZero.ne N)) (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L _ hL) z hz κ _
    ((GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion N (vmul y α)).2.2 hy')

end GlobalTheory.HilbFam
