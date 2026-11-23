import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem loc_gmap (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) :=
  (Formalism.HermitianLatticesTheory.gmap_locS_comm g (Formalism.HermitianLatticesTheory.hcompl (K := K) p) L).symm

theorem gmap_injective (g : V ≃ₗ[K] V) :
    Function.Injective (Formalism.HermitianLatticesTheory.gmap g : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by
  intro A B hAB
  rw [← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g A, ← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g B, hAB]

theorem isUnimodularAt_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (Formalism.HermitianLatticesTheory.gmap g L) ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [loc_gmap, Formalism.HermitianLatticesTheory.genusCovolBound_dualAt_gmap h g hg]
  exact (gmap_injective g).eq_iff

theorem isUnimodularAt_of_loc_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (p : Ideal (𝓞 K))
    {L M : Submodule (𝓞 K) V} (he : Formalism.HermitianLatticesTheory.loc (K := K) p L = Formalism.HermitianLatticesTheory.loc (K := K) p M) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p L ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p M := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [he]

theorem unimodular_of_mem_genus_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Submodule.IsLattice K L ∧ ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by
  refine ⟨hL.1, fun p hp => ?_⟩
  obtain ⟨g, hg, hgI⟩ := hL.2 p hp
  rw [← loc_gmap] at hgI
  rw [← isUnimodularAt_of_loc_eq p hgI, isUnimodularAt_gmap hg]
  exact isUnimodularAt_of_ortho hK hs hI p hp

end ReciprocityTheory.ChartRestriction.L3
