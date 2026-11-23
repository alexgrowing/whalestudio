import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPower
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_augmentation_one_pth_power : ∀ (B : Type) [CommRing B] (p : ℕ) [Fact p.Prime], (p : B) = 0 → ∀ e : Jet B Unit p, (jetAug : Jet B Unit p →ₐ[B] B) e = 1 → ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | exact GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add <;> assumption)
