import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplex
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCMPairingFamily_of_polarisationDiagonal_complex : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ω : ℂ) (C : Ell H ℂ ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp ℂ)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)), IsKForm D ε h → (∀ x ∈ L, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → PureType.IsHomFamily T.t C.P.A C.P.L C.v L (2 * ω - 1) Set.univ ψ → IsFam C T h L ψ := by
  first | exact @GlobalTheory.CM.FamPairing.isFam_of_isHomFamily | exact GlobalTheory.CM.FamPairing.isFam_of_isHomFamily | (intros; apply GlobalTheory.CM.FamPairing.isFam_of_isHomFamily <;> assumption)
