import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory

theorem dense_fromSpec_image_of_sInf_asIdeal_eq_bot :
    ∀ (X : Scheme.{0}) [IsIntegral X] (V : X.Opens) (hV : IsAffineOpen V), (V : Set X).Nonempty →
    ∀ (M : Set (PrimeSpectrum Γ(X, V))), sInf (PrimeSpectrum.asIdeal '' M) = ⊥ → Dense (hV.fromSpec '' M) := by
  intro X _ V hV hne M hM
  have hMd : Dense M := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    have : PrimeSpectrum.vanishingIdeal M = ⊥ := by
      rw [← hM]
      apply le_antisymm
      · intro f hf
        rw [Submodule.mem_sInf]
        rintro _ ⟨p, hp, rfl⟩
        exact (PrimeSpectrum.mem_vanishingIdeal M f).1 hf p hp
      · intro f hf
        rw [PrimeSpectrum.mem_vanishingIdeal]
        intro p hp
        rw [Submodule.mem_sInf] at hf
        exact hf _ ⟨p, hp, rfl⟩
    rw [this, PrimeSpectrum.zeroLocus_bot]
  have hr : DenseRange hV.fromSpec := by
    have h1 : Set.range hV.fromSpec = (V : Set X) := hV.range_fromSpec
    unfold DenseRange
    rw [h1]
    exact V.2.dense hne
  exact hr.dense_image hV.fromSpec.continuous hMd

end GlobalTheory
