import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.TraitPull

theorem exists_pull_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  intro E _ _ _ H Dw l Xo c T W _ _ _ hW hWd h hi hl
  obtain ⟨tW, ⟨m⟩⟩ := GlobalTheory.Models.Inhab.exists_pull (spMap h) T.t
  obtain ⟨PW, e, he⟩ := GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hW hWd h hi hl tW ⟨m⟩
  refine ⟨tW, m, PW, e, fun y => ?_⟩
  obtain ⟨u, n, hn, hc⟩ := T.mono (e y)
  have hn0 : T.be (e y) (e y) = 2 * (n 0 : ℤ) := hn 0
  obtain ⟨v, hv⟩ := he y _ hc
  refine ⟨by rw [hn0]; positivity, _, hv, ?_⟩
  have ht : (T.be (e y) (e y)).toNat = 2 * n 0 := by rw [hn0]; omega
  rw [ht]
  have hu : IsUnit ((v : W) * h u) := v.isUnit.mul (u.isUnit.map h)
  have e1 : ((v : W) * h (u * ∏ i, ![T.ϖ] i ^ n i)) ^ 2 = ((v : W) * h u) ^ 2 * h T.ϖ ^ (2 * n 0) := by
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
    ring
  rw [e1]
  exact associated_unit_mul_left _ _ (hu.pow 2)

end GlobalTheory.UPoinc.TraitPull
