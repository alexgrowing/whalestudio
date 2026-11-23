import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityBaseChangeProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibility_base_change_projective : ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] [IsDomain A'] [IsIntegrallyClosed A'] [IsDomain B] [Algebra A A'] [Algebra A B] [Algebra.IsIntegral A B] (g : A' →+* B), Function.Injective g → (∀ a, g (algebraMap A A' a) = algebraMap A B a) → (∀ a x : A', g a ∣ g x → a ∣ x) ∧ ∀ (N N' : Type) [AddCommGroup N] [Module A N] [Module.Projective A N] [AddCommGroup N'] [Module A' N'] (e : A' ⊗[A] N ≃ₗ[A'] N') (l : N' →ₛₗ[g] B ⊗[A] N), (∀ y, l (e (1 ⊗ₜ y)) = 1 ⊗ₜ y) → ∀ (a : A') (y : N'), l y ∈ g a • (⊤ : Submodule B (B ⊗[A] N)) → y ∈ a • (⊤ : Submodule A' N') := by
  first | exact @GlobalTheory.ChainDesc.dvd_of_map_dvd_and_mem_smul_top | exact GlobalTheory.ChainDesc.dvd_of_map_dvd_and_mem_smul_top | (intros; apply GlobalTheory.ChainDesc.dvd_of_map_dvd_and_mem_smul_top <;> assumption)
