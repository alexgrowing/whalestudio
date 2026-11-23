import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRegularThetaSetupCover
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_regular_thetaSetup_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), (∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) → ∃ (m : ℕ) (X' : Fin m → USetup C) (U : ∀ k, (X' k).M.Z.Opens), (∀ k, (X' k).S.R ≤ (X' k).M.ringOn (U k)) ∧ ∀ x : Xo.XF c, ∃ k, ∃ w ∈ U k, (X' k).π w = C.i x := by
  first | exact @GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover | exact GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover | (intros; apply GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover <;> assumption)
