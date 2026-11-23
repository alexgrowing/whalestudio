import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemKummerNormsOfLocalNormsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemUnitsLocalKummerNormsOfBaseChangeNormStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [Field E] [Algebra F E]
    [IsGalois F E] (ζ : F) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hr : Module.finrank F E = p) :
    ∃ (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (hr ▸ hp.pos)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hr])
  have hK : (primitiveRoots (Module.finrank F E) F).Nonempty :=
    ⟨ζ, by rw [hr, mem_primitiveRoots hp.pos]; exact hζ⟩
  obtain ⟨θ, ⟨δ, hδ⟩, hθ⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hK
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hδ.symm hθ
  rw [hr] at hirr hδ
  have hmin : (X ^ p - C δ : F[X]) = minpoly F θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hδ]) (monic_X_pow_sub_C _ hp.ne_zero)
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := F) (L := E) (x := algebraMap F E ζ * θ)
    (y := θ) (Algebra.IsAlgebraic.isAlgebraic θ) (by
      rw [← hmin]
      rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul,
        hδ, sub_self])
  refine ⟨δ, θ, σ, hp, hζ, (X_pow_sub_C_irreducible_iff_of_prime hp).1 hirr, hδ.symm, hσ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic θ), hθ, IntermediateField.top_toSubalgebra]

theorem np_of_finrank_prime_of_isPrimitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsGalois F E] (ζ : F), p.Prime → IsPrimitiveRoot ζ p → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ _ ζ hp hζ hr x hx hloc
  classical
  obtain ⟨δ, θ, σ, hk⟩ := exists_isKum_of_finrank_prime p F E ζ hp hζ hr
  have hδ0 : δ ≠ 0 := fun h => hk.nonpow 0 (by rw [h, zero_pow hp.ne_zero])
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ0, Units.mk0 x hx} ∅
  obtain ⟨S, hS, hadm⟩ := (exists_admissiblePlaces_superset_and_mono p F hp.pos).1 S₁
  have hfin : Units.mk0 x hx ∈ finNorm p F δ S := by
    simp only [finNorm, Subgroup.mem_iInf]
    intro v _
    exact GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm p F E (v.adicCompletion F) ζ δ θ σ hk (Units.mk0 x hx) (hloc.1 v)
  have hx' := GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms p F ζ (Units.mk0 δ hδ0) S hp hζ hadm (hS₁ S hS _ (by simp))
    hk.nonpow (Units.mk0 x hx) (hS₁ S hS _ (by simp)) hfin
  obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ _).1 hx'
  obtain ⟨-, -, -, -, -, ⟨e⟩, -⟩ := kummer_galois p F E ζ δ θ σ hk
  refine ⟨e.symm y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv]
  exact hy

end GlobalTheory.CNorm
