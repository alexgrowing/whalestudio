import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_diagonal_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (c' : 𝔠.elt) (l l' : u.Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n := by
  first | exact @GlobalTheory.RiemInt.riemannForm_int | exact GlobalTheory.RiemInt.riemannForm_int | (intros; apply GlobalTheory.RiemInt.riemannForm_int <;> assumption)
