import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystems
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem homLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B] (φ : B₀ →ₐ[R₀] B₀'), ∃ ρ : B →ₐ[R] B', ∀ b, p' (ρ b) = φ (p b) := by
  intro R R₀ _ _ I hI π _ _ B B₀ _ _ _ _ p hs _ _ B' B₀' _ _ _ _ p' hs' hp' hker' _ φ
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  letI : Algebra R B₀' := ((algebraMap R₀ B₀').comp π).toAlgebra
  let P : B →ₐ[R] B₀' := { (φ : B₀ →+* B₀').comp p with
    commutes' := fun r ↦ by
      show φ (p (algebraMap R B r)) = algebraMap R₀ B₀' (π r)
      rw [hs.map_algebraMap r]
      exact φ.commutes (π r) }
  let P' : B' →ₐ[R] B₀' := { p' with commutes' := fun r ↦ hs'.map_algebraMap r }
  have hn := LocalIsomorphism.nil I P' hker' (map_sq hI B')
  exact ⟨Algebra.FormallySmooth.liftOfSurjective P P' hp' hn,
    fun b ↦ Algebra.FormallySmooth.liftOfSurjective_apply P P' hp' hn b⟩

end GlobalTheory.Obs
