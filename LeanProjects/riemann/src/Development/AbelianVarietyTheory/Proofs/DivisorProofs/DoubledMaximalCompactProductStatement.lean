import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledMaximalCompactProduct
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
theorem _root_.GlobalTheory.T.glue_local_elements : ∀ (B : Type) [CommRing B] (s : Set B), (∀ P : PrimeSpectrum B, ∃ f ∈ s, f ∉ P.asIdeal) → ∀ v : ∀ f : s, Localization.Away (f : B), (∀ (f g : s) (D : Type) [CommRing D] [Algebra B D] (α : Localization.Away (f : B) →ₐ[B] D) (β : Localization.Away (g : B) →ₐ[B] D), α (v f) = β (v g)) → ∃ b : B, ∀ f : s, algebraMap B (Localization.Away (f : B)) b = v f := by
  first | exact @GlobalTheory.localizationAway_glue_of_forall_prime | exact GlobalTheory.localizationAway_glue_of_forall_prime | (intros; apply GlobalTheory.localizationAway_glue_of_forall_prime <;> assumption)
