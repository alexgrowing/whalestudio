import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsInvariantOfSplitZerosTorsionStatement
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_enum_torsion (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (x : KeyIn K) (N : ℕ)
    (hN : (N : K) ≠ 0) : ∃ ξ : Fin (N ^ (2 * x.P.g)) → Pt x, (∀ a, ξ a ^ N = 1) ∧
      ∀ a a', a ≠ a' → ∀ p : Sp K, (ξ a).left p ≠ (ξ a').left p := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  have hc : Nat.card {y : Pt x // y ^ N = 1} = N ^ (2 * x.P.g) :=
    (hL.mulN _ x.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 K (𝟙 _) hN
  have : Finite {y : Pt x // y ^ N = 1} := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ hN0)
  let e := (Finite.equivFinOfCardEq hc).symm
  refine ⟨fun a => (e a).1, fun a => (e a).2, fun a a' h p hp => h (e.injective (Subtype.ext ?_))⟩
  have := x.P.isAb.proper
  obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) hp)

theorem exists_kaVal_of_isAlgClosed : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), admitted x.P.g n l l' al → ((degProd x.P.g n l l' : ℕ) : K) ≠ 0 → EtZ x s z ch → ∃ κ, KaVal x n l l' al s κ := by
  intro hL K _ _ x n l l' al d s z ch hA hN hZ
  obtain ⟨ξ, h₁, h₂⟩ := exists_enum_torsion hL x _ hN
  exact GlobalTheory.T.exists_invariant_of_split_zeros_torsion hL K x n l l' al d s z ch ξ hA (Ne.isUnit hN) hZ h₁ h₂

end GlobalTheory.KeyKa
