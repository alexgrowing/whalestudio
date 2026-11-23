import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ringKrullDim_le_of_isEtaleCompletion : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  intro O A _ _ _ _ _ _ ψ _ h
  letI : Algebra O A := ψ.toAlgebra
  have hmap : (maximalIdeal O).map (algebraMap O A) = maximalIdeal A := h.2.1
  have hlo : (maximalIdeal A).LiesOver (maximalIdeal O) := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    exact (IsLocalRing.maximalIdeal_comap ψ).symm
  have key := Ideal.height_le_height_add_of_liesOver (maximalIdeal O) (maximalIdeal A)
  rw [hmap, Ideal.map_quotient_self] at key
  have h0 : (⊥ : Ideal (A ⧸ maximalIdeal A)).height = 0 := by
    simp
  rw [h0, add_zero] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast key
