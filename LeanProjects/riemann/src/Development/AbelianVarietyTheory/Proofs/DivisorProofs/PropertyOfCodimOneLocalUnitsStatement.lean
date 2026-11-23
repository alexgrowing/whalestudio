import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.property_of_codim_one_local_units : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (P : ∀ (k : Type) [Field k], (A →+* k) → k → Prop) (good : Set (PrimeSpectrum A)),
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ good →
    (∀ 𝔭 : PrimeSpectrum A, (𝔭 ∈ good ∨ 𝔭.asIdeal.height = 1) → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), P k (φ.comp (algebraMap A _)) (φ u)) →
    (∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', P k φ v → P k φ v' → v = v') →
    (∀ (k : Type) [Field k] (φ : A →+* k) (v : k),
      (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∉ good → P k φ v) →
    ∃ f : Aˣ, ∀ (k : Type) [Field k] (φ : A →+* k), P k φ (φ f) := by
  first | exact @GlobalTheory.HartogsUnit.exists_unit_of_local_units | exact GlobalTheory.HartogsUnit.exists_unit_of_local_units | (intros; apply GlobalTheory.HartogsUnit.exists_unit_of_local_units <;> assumption)
