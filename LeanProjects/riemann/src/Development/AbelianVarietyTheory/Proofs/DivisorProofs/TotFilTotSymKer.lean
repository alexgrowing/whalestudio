import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilVSymVKer
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_totSym_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, totFil X s (a + 1) ≤ totFil X s a ∧ ∀ x : totFil X s a, totSym Co a x = 0 ↔ x.1 ∈ totFil X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  obtain ⟨hle, hker⟩ := GlobalTheory.HSCore.filV_symV_ker K X s hs δ Co a ha
  refine ⟨Submodule.map_mono hle, fun x => ?_⟩
  let e := Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)
  let y : filV X s a := e.symm x
  have hxy : e y = x := e.apply_symm_apply x
  have hx1 : x.1 = incl X X.T y.1 := by rw [← hxy]; rfl
  have : totSym Co a x = symV Co a y := rfl
  rw [this, hker y, hx1]
  constructor
  · intro h
    exact ⟨y.1, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← incl_injective X X.T hzy]

end GlobalTheory.HSShort
