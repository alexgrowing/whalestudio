import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential IsLocalRing TensorProduct

namespace GlobalTheory

theorem span_D_uniformizer_transcendenceBasis : ∀ (k R : Type) [Field k] [CharZero k] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] [Algebra.EssFiniteType k R] (s : R),
    Irreducible s → ∀ (m : ℕ) (y : Fin m → R),
    IsTranscendenceBasis k (fun j => IsLocalRing.residue R (y j)) →
    Submodule.span R (insert (D k R s) (Set.range fun j => D k R (y j))) = ⊤ := by
  intro k R _ _ _ _ _ _ _ s hs m y hy
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := residue_surjective
  haveI := hy.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun j => residue R (y j)))
      (ResidueField R) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hy.1
  have hmax : maximalIdeal R = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).1 hs
  have hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := ker_residue
  have hs0 : algebraMap R (ResidueField R) s = 0 := by
    rw [← RingHom.mem_ker, hker, hmax]; exact Ideal.mem_span_singleton_self s
  haveI : Module.Finite R Ω[R⁄k] := inferInstance
  set N := Submodule.span R (insert (D k R s) (Set.range fun j => D k R (y j))) with hN
  have hmb : ∀ x : R, mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] D k R x) =
      D k (ResidueField R) (algebraMap R (ResidueField R) x) :=
    fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
  have key : ∀ ω : Ω[R⁄k], ∃ n ∈ N, (1 : ResidueField R) ⊗ₜ[R] ω = (1 : ResidueField R) ⊗ₜ[R] n := by
    intro ω
    let c := b.repr (mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] ω))
    let c' : Fin m → R := fun i => Function.surjInv hsurj (c i)
    have hc' : ∀ i, algebraMap R (ResidueField R) (c' i) = c i := fun i => Function.surjInv_eq hsurj _
    have h0 : mapBaseChange k R (ResidueField R)
        ((1 : ResidueField R) ⊗ₜ[R] (ω - ∑ i, c' i • D k R (y i))) = 0 := by
      rw [tmul_sub, map_sub, tmul_sum, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] ω))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, tmul_smul, ← algebraMap_smul (ResidueField R) (c' i), map_smul, hmb, hc']
      rfl
    obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) hsurj _).mp h0
    obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
    have ha' := ha
    rw [hker, hmax, Ideal.mem_span_singleton'] at ha'
    obtain ⟨r, rfl⟩ := ha'
    rw [kerCotangentToTensor_toCotangent] at ht
    have e1 : (1 : ResidueField R) ⊗ₜ[R] D k R (r * s) = (1 : ResidueField R) ⊗ₜ[R] (r • D k R s) := by
      rw [Derivation.leibniz, tmul_add, add_eq_left]
      have : (1 : ResidueField R) ⊗ₜ[R] (s • D k R r) = (algebraMap R (ResidueField R) s) • ((1 : ResidueField R) ⊗ₜ[R] D k R r) := by
        rw [algebraMap_smul, tmul_smul]
      rw [this, hs0, zero_smul]
    refine ⟨r • D k R s + ∑ i, c' i • D k R (y i), ?_, ?_⟩
    · exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)))
    · have e2 : ω = (ω - ∑ i, c' i • D k R (y i)) + ∑ i, c' i • D k R (y i) := (sub_add_cancel _ _).symm
      rw [e2, tmul_add, ← ht, e1, ← tmul_add]
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, eq_top_iff]
  intro z _
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c ω =>
    obtain ⟨c₀, rfl⟩ := hsurj c
    obtain ⟨n, hn, hω⟩ := key ω
    refine ⟨c₀ • n, N.smul_mem _ hn, ?_⟩
    rw [LinearMap.map_smul, TensorProduct.mk_apply, ← hω, ← algebraMap_smul (ResidueField R) c₀,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x z hx hz => exact add_mem (hx trivial) (hz trivial)

end GlobalTheory
