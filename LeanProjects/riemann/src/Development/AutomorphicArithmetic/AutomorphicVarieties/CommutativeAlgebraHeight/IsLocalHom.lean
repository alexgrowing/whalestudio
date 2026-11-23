import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain

noncomputable section

open IsLocalRing

namespace UpperTheory.V.CA

structure IsCL (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] : Prop where
  noeth : IsNoetherianRing R
  complete : IsAdicComplete (maximalIdeal R) R
  isLocalHom : IsLocalHom (algebraMap O R)
  res_fin : Module.Finite O (ResidueField R)

theorem IsCL.of_isCO (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Alg.IsCO O R] :
    IsCL O R := by
  refine ⟨inferInstance, UpperTheory.V.Alg.IsCO.complete (O := O), UpperTheory.V.Alg.IsCO.isLocalHom, ?_⟩
  refine Module.Finite.of_surjective (Algebra.linearMap O (ResidueField R)) ?_
  intro y
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) r
  refine ⟨a, ?_⟩
  rw [Algebra.linearMap_apply, IsScalarTower.algebraMap_apply O R (ResidueField R),
    ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have h' := (maximalIdeal R).neg_mem ha
  rwa [neg_sub] at h'

section Cpl

variable {C : Type} [CommRing C] (x : Ideal C) [x.IsPrime]

abbrev Cpl : Type := AdicCompletion (maximalIdeal (Localization.AtPrime x)) (Localization.AtPrime x)

def toCpl : C →+* Cpl x :=
  (algebraMap (Localization.AtPrime x) (Cpl x)).comp (algebraMap C (Localization.AtPrime x))

def dimAt (I : Ideal C) : WithBot ℕ∞ :=
  ringKrullDim (Localization.AtPrime x ⧸ I.map (algebraMap C (Localization.AtPrime x)))

end Cpl

structure IsCplAt {C : Type} [CommRing C] (x : Ideal C) (R : Type) [CommRing R] [Algebra C R] [IsLocalRing R] :
    Prop where
  noeth : IsNoetherianRing R
  complete : IsAdicComplete (maximalIdeal R) R
  comap_pow : ∀ n : ℕ, (maximalIdeal R ^ n).comap (algebraMap C R) = x ^ n
  dense : ∀ (n : ℕ) (r : R), ∃ c : C, r - algebraMap C R c ∈ maximalIdeal R ^ n

theorem IsCplAt.self (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] : IsCplAt (maximalIdeal R) R where
  noeth := inferInstance
  complete := inferInstance
  comap_pow n := Ideal.comap_id _
  dense n r := ⟨r, by simp⟩

end UpperTheory.V.CA
