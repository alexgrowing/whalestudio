import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAlgHomLocalizationAwayVanish
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_algHom_localizationAway_vanish : ∀ (R K C : Type) [CommRing R] [Field K] [Algebra R K] [CommRing C] [Algebra R C], (∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0) → ∀ (e : C) (y : Localization.Away e), (∀ χ : Localization.Away e →ₐ[R] K, χ y = 0) → y = 0 := by
  first | exact @GlobalTheory.points_separate_localization_away | exact GlobalTheory.points_separate_localization_away | (intros; apply GlobalTheory.points_separate_localization_away <;> assumption)
