import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GramIff

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.irrOpen :
    ∀ {A G ι : Type} [CommRing A] [Group G] [Fintype ι] [DecidableEq ι] (t : G → A),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] (φ : A →+* K) (ρ : G →* Matrix ι ι K) (p : PrimeSpectrum A), p.asIdeal = RingHom.ker φ →
        (∀ g, (ρ g).trace = φ (t g)) → (p ∈ U ↔ Submodule.span K (Set.range ρ) = ⊤) := by
  intro A G ι _ _ _ _ t
  refine ⟨⋃ g : ι × ι → G,
      ((PrimeSpectrum.basicOpen (Matrix.of fun a b => t (g a * g b)).det : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)),
    isOpen_iUnion (fun g => (PrimeSpectrum.basicOpen _).isOpen), ?_⟩
  intro K _ φ ρ p hp htr
  rw [UpperTheory.V.AlgebraTools.Det.gramIff, Set.mem_iUnion]
  apply exists_congr
  intro g
  have hM : φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) =
      Matrix.of fun a b => (ρ (g a * g b)).trace := by
    ext a b
    show φ (t (g a * g b)) = (ρ (g a * g b)).trace
    rw [htr]
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hp, RingHom.mem_ker, RingHom.map_det, hM]
