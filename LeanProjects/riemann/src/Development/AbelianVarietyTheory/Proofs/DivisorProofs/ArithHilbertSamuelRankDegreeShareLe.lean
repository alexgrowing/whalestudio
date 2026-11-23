import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuelStatement

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem share_le_of_rankLow (h : RankLow) (F : Type) [Field F] [NumberField F] (X : Data F)
    (hn : IsNef F X.LA) (hb : IsBig F X.LA) : (X.R : ℤ) * X.del ≤ X.d := by
  refine (h F X.toGeo hn hb X.T).trans ?_
  rw [X.d_eq_finrank]
  exact_mod_cast Submodule.finrank_mono (X.global_le X.T le_rfl)

theorem share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F),
    IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d :=
  fun q => share_le_of_rankLow (GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel q)

end GlobalTheory.HSCore
