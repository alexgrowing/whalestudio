import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem filV_symV_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, filV X s (a + 1) ≤ filV X s a ∧ ∀ x : filV X s a, symV Co a x = 0 ↔ x.1 ∈ filV X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  have haT : a ≤ X.T := by omega
  refine ⟨Submodule.comap_mono (Vanishing.Fil_anti (Nat.le_succ a)), fun x => ?_⟩
  have key : symV Co a x = 0 ↔ hs.sym (Nat.sub_add_cancel haT) (spaceV X s)
      ((X.V X.T).subtype.restrict (fun _ hx => hx) x) = 0 := by
    unfold symV
    rw [dif_pos haT]
    constructor
    · intro h
      funext α
      apply (Co.ev (X.T - a)).injective
      funext p
      have := congrFun h (α, p)
      simpa using this
    · intro h
      funext q
      simp [h]
  rw [key]
  exact Vanishing.sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _

end GlobalTheory.HSCore
