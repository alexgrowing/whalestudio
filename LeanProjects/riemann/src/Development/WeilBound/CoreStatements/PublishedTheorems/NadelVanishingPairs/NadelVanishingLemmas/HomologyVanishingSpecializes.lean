import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomologyVanishingSpecializes
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.homology_vanishing_specializes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ), (∀ p, n < p → IsZero (C.X p)) → (∀ p, Module.Flat R (C.X p)) → (∀ p, Module.Finite R (C.homology p)) → ∀ (κ₁ κ₂ : Type) [Field κ₁] [Field κ₂] (g₁ : R →+* κ₁) (g₂ : R →+* κ₂), RingHom.ker g₂ ≤ RingHom.ker g₁ → ∀ q : ℕ, Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g₁).mapHomologicalComplex _).obj C).homology q) → Subsingleton ((((ModuleCat.extendScalars.{0, 0, 0} g₂).mapHomologicalComplex _).obj C).homology q) := by
  first | exact @_root_.GlobalTheory.FibreVanishGen.main | exact _root_.GlobalTheory.FibreVanishGen.main | (intros; apply _root_.GlobalTheory.FibreVanishGen.main <;> assumption)
