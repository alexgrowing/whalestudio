import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_flag_hodge_index_vanishing : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x → ∀ N : ι → GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, (∀ k, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) → ∀ M : ι → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  first | exact @GlobalTheory.FlagTan.isKS_dir_sum | exact GlobalTheory.FlagTan.isKS_dir_sum | (intros; apply GlobalTheory.FlagTan.isKS_dir_sum <;> assumption)
