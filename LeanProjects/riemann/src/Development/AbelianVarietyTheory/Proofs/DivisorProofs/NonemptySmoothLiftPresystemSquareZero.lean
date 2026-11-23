import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem pre_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  intro R R₀ _ _ I hI π hπ hk C _ F hF
  have h := fun T => GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening R R₀ I hI π hπ hk (F.obj T) (hF T)
  choose B iB aB p hs hp hker hsm using h
  letI := iB
  letI := aB
  have hl : ∀ {T T' : C} (a : T ⟶ T'), ∃ ρ : B T →ₐ[R] B T', ∀ b, p T' (ρ b) = mp F a (p T b) :=
    fun {T T'} a => homLift R R₀ I hI π hπ hk (B T) (F.obj T) (p T) (hs T) (hp T) (hker T)
      (B T') (F.obj T') (p T') (hs T') (hp T') (hker T') (mp F a)
  exact ⟨{ B := fun T => CommAlgCat.of R (B T)
           p := p
           semi := hs
           surj := hp
           ker := hker
           smooth := hsm
           ρ := fun a => (hl a).choose
           nat := fun a b => (hl a).choose_spec b }⟩

end GlobalTheory.Obs
