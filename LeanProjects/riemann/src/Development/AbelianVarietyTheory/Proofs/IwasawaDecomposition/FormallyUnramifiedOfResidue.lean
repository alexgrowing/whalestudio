import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem formallyUnramified_of_finite_map_maximalIdeal
    {A B R : Type} [CommRing A] [CommRing B] [IsLocalRing B] [CommRing R] [IsLocalRing R]
    (ι : A →+* B) (ψ : B →+* R) (hψ : ψ.Finite) (hm : (maximalIdeal B).map ψ = maximalIdeal R)
    (hu : ((residue R).comp (ψ.comp ι)).FormallyUnramified) : ψ.FormallyUnramified := by
  have hloc : IsLocalHom ψ := by
    refine ⟨fun b hb => ?_⟩
    by_contra h
    have hb' : b ∈ maximalIdeal B := (mem_maximalIdeal b).2 h
    have : ψ b ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem ψ hb'
    exact (mem_maximalIdeal _).1 this hb
  algebraize [ψ, ι, ψ.comp ι]
  have h1 : Algebra.FormallyUnramified A (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    exact hu
  have h2 : Algebra.FormallyUnramified B (ResidueField R) := .of_restrictScalars A _ _
  have h3 : Algebra.FormallyUnramified (ResidueField B) (ResidueField R) := .of_restrictScalars B _ _
  have h4 : Algebra.EssFiniteType B (ResidueField R) := .comp _ R _
  have h5 : Algebra.EssFiniteType (ResidueField B) (ResidueField R) := .of_comp B _ _
  have h6 : Algebra.IsSeparable (ResidueField B) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  have h7 : Algebra.FormallyUnramified B R := Algebra.FormallyUnramified.of_map_maximalIdeal hm
  exact RingHom.formallyUnramified_algebraMap.2 h7

end GlobalTheory
