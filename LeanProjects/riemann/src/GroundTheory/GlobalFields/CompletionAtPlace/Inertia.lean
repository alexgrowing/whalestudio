import Mathlib
import GroundTheory.GlobalFields.CompletionAtPlace.Galois
import GroundTheory.LocalFields.Ramification

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField

open scoped WithZero Pointwise

namespace GroundTheory.Global

section Residue

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem exists_sub_ringOfIntegersToInteger_mem (x : 𝒪[u.adicCompletion F]) :
    ∃ r : 𝓞 F, x - ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] := by
  obtain ⟨r, hr⟩ := toResidueInteger_surjective u (Ideal.Quotient.mk _ x)
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

theorem ringOfIntegersToInteger_mem_maximalIdeal_iff (r : 𝓞 F) :
    ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] ↔ r ∈ u.asIdeal := by
  rw [← ker_toResidueInteger u, RingHom.mem_ker, toResidueInteger, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem natCard_residueField_integer :
    Nat.card 𝓀[u.adicCompletion F] = Nat.card (𝓞 F ⧸ u.asIdeal) :=
  (Nat.card_congr (residueEquivInteger u).toEquiv).symm

end Residue

section Inertia

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem integerAlgEquiv_ringOfIntegersToInteger (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (r : 𝓞 L) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) (decompositionToLocal v w σ)
        (ringOfIntegersToInteger w r) = ringOfIntegersToInteger w ((σ : Gal(L/K)) • r) := by
  apply Subtype.ext
  rw [coe_integerAlgEquiv_apply, coe_ringOfIntegersToInteger, coe_ringOfIntegersToInteger,
    decompositionToLocal_algebraMap]
  rfl

theorem integerAlgEquiv_mem_maximalIdeal_iff (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) τ x ∈ 𝓂[w.adicCompletion L] ↔
      x ∈ 𝓂[w.adicCompletion L] := by
  simpa using integerAlgEquiv_mem_maximalIdeal_pow_iff τ 1 x

theorem mem_inertia_iff_decompositionToLocal_mem (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) ∈ w.asIdeal.inertia Gal(L/K) ↔
      decompositionToLocal v w σ ∈
        lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by
  have h0 : ((0 : ℕ) : ℤ) = 0 := rfl
  rw [← h0, mem_lowerRamificationGroup_natCast_iff, zero_add, pow_one]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ∈ w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    rw [map_sub] at h1
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r) - (x - ringOfIntegersToInteger w r) := by
      ring
    rw [this]
    exact sub_mem (add_mem h1 h2) hr
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this

end Inertia

section Frobenius

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

def arithFrobAtDecomposition : MulAction.stabilizer Gal(L/K) w.asIdeal :=
  ⟨arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal, IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) w.asIdeal⟩

omit [NumberField L] [IsGalois K L] [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in

theorem natCard_residueField_eq_under :
    Nat.card 𝓀[v.adicCompletion K] = Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) := by
  rw [natCard_residueField_integer v, ← Ideal.over_def w.asIdeal v.asIdeal]

theorem isArithFrobAt_iff_decompositionToLocal (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal ↔
      ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈
          𝓂[w.adicCompletion L] := by
  rw [natCard_residueField_eq_under v w]
  change (∀ r : 𝓞 L, (σ : Gal(L/K)) • r - r ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈
    w.asIdeal) ↔ _
  constructor
  · intro h x
    obtain ⟨r, hr⟩ := exists_sub_ringOfIntegersToInteger_mem w x
    set q := Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K))
    have h1 := (integerAlgEquiv_mem_maximalIdeal_iff v w (decompositionToLocal v w σ) _).2 hr
    rw [map_sub] at h1
    have h2 : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
          ringOfIntegersToInteger w r ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
        ringOfIntegersToInteger_mem_maximalIdeal_iff]
      exact h r
    have h3 : ringOfIntegersToInteger w r ^ q - x ^ q ∈ 𝓂[w.adicCompletion L] := by
      rw [← Ideal.Quotient.eq, map_pow, map_pow, Ideal.Quotient.eq.2 hr]
    have : integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ q =
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) x - integerAlgEquiv (v.adicCompletion K)
            (w.adicCompletion L) (decompositionToLocal v w σ) (ringOfIntegersToInteger w r)) +
        (integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
          (decompositionToLocal v w σ) (ringOfIntegersToInteger w r) -
            ringOfIntegersToInteger w r ^ q) + (ringOfIntegersToInteger w r ^ q - x ^ q) := by
      ring
    rw [this]
    exact add_mem (add_mem h1 h2) h3
  · intro h r
    have := h (ringOfIntegersToInteger w r)
    rwa [integerAlgEquiv_ringOfIntegersToInteger, ← map_pow, ← map_sub,
      ringOfIntegersToInteger_mem_maximalIdeal_iff] at this

theorem decompositionToLocal_arithFrobAt (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w (arithFrobAtDecomposition w)) x -
      x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L] :=
  (isArithFrobAt_iff_decompositionToLocal v w _).1 (IsArithFrobAt.arithFrobAt _ _ _) x

omit [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in

theorem natCard_inertia :
    Nat.card (w.asIdeal.inertia Gal(L/K)) = w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)]

theorem eq_decompositionToLocal_arithFrobAt (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (hτ : ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
      τ x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L]) :
    τ = decompositionToLocal v w (arithFrobAtDecomposition w) := by
  obtain ⟨σ, rfl⟩ := (decompositionToLocal_bijective v w).2 τ
  congr 1
  have hσ : IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal :=
    (isArithFrobAt_iff_decompositionToLocal v w σ).2 hτ
  have hmem := hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal)
  have hbot : w.asIdeal.inertia Gal(L/K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ ((natCard_inertia v w).trans he)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact Subtype.ext hmem

end Frobenius

section InertiaGalois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem map_inertia_decompositionMulEquiv :
    ((w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)).map
        (decompositionMulEquiv v w).toMonoidHom =
      lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by
  ext τ
  obtain ⟨σ, rfl⟩ := (decompositionMulEquiv v w).surjective τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ', hσ', h⟩
    rw [← h]
    exact (mem_inertia_iff_decompositionToLocal_mem v w σ').1 (Subgroup.mem_subgroupOf.1 hσ')
  · intro h
    exact ⟨σ, Subgroup.mem_subgroupOf.2 ((mem_inertia_iff_decompositionToLocal_mem v w σ).2 h),
      rfl⟩

end InertiaGalois

end GroundTheory.Global
