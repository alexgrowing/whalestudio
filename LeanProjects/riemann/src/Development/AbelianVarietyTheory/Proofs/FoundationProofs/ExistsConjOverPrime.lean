import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.ValConjClosure

theorem valuation_intCast_eq_one {Ω : Type} [Field Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : A.valuation (n : Ω) = 1 := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  refine le_antisymm (hle n) (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hn
  have hab' : (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have h1 : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) :=
          mul_le_mul' (hle a) le_rfl
      _ < 1 := by rwa [one_mul]
  have h2 : A.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) :=
          mul_le_mul' (hle b) le_rfl
      _ < 1 := by rwa [one_mul]
  have hadd := A.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
  rw [hab', map_one] at hadd
  exact absurd hadd (not_le.mpr (max_lt h1 h2))

theorem ratCast_mem_iff {Ω : Type} [Field Ω] [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (a : ℚ) : (a : Ω) ∈ A ↔ ¬ p ∣ a.den := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hden0 : (a.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  rw [Rat.cast_def, ← A.valuation_le_one_iff]
  constructor
  · intro ha hd
    have hnum : ¬ (p : ℤ) ∣ a.num := by
      intro h
      have h1 : p ∣ a.num.natAbs := Int.natCast_dvd.mp h
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 a.reduced) hd)
    have hv1 := valuation_intCast_eq_one hp A hA a.num hnum
    obtain ⟨k, hk⟩ := hd
    have hdlt : A.valuation (a.den : Ω) < 1 := by
      rw [hk, Nat.cast_mul, map_mul]
      calc A.valuation (p : Ω) * A.valuation (k : Ω) ≤ A.valuation (p : Ω) * 1 :=
            mul_le_mul' le_rfl (by exact_mod_cast hle k)
        _ < 1 := by rwa [mul_one]
    have hnd : A.valuation (a.num : Ω) ≤ A.valuation (a.den : Ω) := by
      rw [← div_mul_cancel₀ (a.num : Ω) hden0, map_mul]
      calc A.valuation ((a.num : Ω) / (a.den : Ω)) * A.valuation (a.den : Ω) ≤
            1 * A.valuation (a.den : Ω) := mul_le_mul' ha le_rfl
        _ = A.valuation (a.den : Ω) := one_mul _
    rw [hv1] at hnd
    exact absurd (lt_of_le_of_lt hnd hdlt) (lt_irrefl 1)
  · intro hd
    have hv1 : A.valuation (a.den : Ω) = 1 := by
      have h := valuation_intCast_eq_one hp A hA (a.den : ℤ) (by exact_mod_cast hd)
      exact_mod_cast h
    rw [map_div₀, hv1, div_one]
    exact hle a.num

theorem isClosed_apply_mem {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (x : Ω) (T : Set Ω) : IsClosed {σ : Ω ≃ₐ[F] Ω | σ x ∈ T} := by
  let E := IntermediateField.adjoin F ({x} : Set Ω)
  haveI : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (E.fixingSubgroup : Set (Ω ≃ₐ[F] Ω)), ?_,
    E.fixingSubgroup_isOpen.preimage (continuous_mul_left σ⁻¹), ?_⟩
  · intro τ hτ hT
    apply hσ
    have hfix : (σ⁻¹ * τ) x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x
      (IntermediateField.mem_adjoin_simple_self F x)
    have hinv : ∀ y, σ (σ⁻¹ y) = y := fun y => by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply] at hfix
    have he : τ x = σ x :=
      calc τ x = σ (σ⁻¹ (τ x)) := (hinv _).symm
        _ = σ x := by rw [hfix]
    change σ x ∈ T
    rw [← he]
    exact hT
  · show σ⁻¹ * σ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact E.fixingSubgroup.one_mem

theorem exists_conj_of_isGalois {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (A B : ValuationSubring Ω) (h : ∀ a : F, algebraMap F Ω a ∈ A ↔ algebraMap F Ω a ∈ B) :
    ∃ σ : Ω ≃ₐ[F] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  let C : Finset Ω → Set (Ω ≃ₐ[F] Ω) := fun s => {σ | ∀ x ∈ s, σ x ∈ B ↔ x ∈ A}
  have hclosed : ∀ s, IsClosed (C s) := by
    intro s
    have hC : C s = ⋂ x ∈ s, {σ : Ω ≃ₐ[F] Ω | σ x ∈ {y : Ω | y ∈ B ↔ x ∈ A}} := by
      ext σ
      simp [C]
    rw [hC]
    exact isClosed_biInter fun x _ => isClosed_apply_mem x _
  have hne : ∀ s, (C s).Nonempty := by
    intro s
    let L := (FiniteGaloisIntermediateField.adjoin F (s : Set Ω)).toIntermediateField
    have hsL : (s : Set Ω) ⊆ L := FiniteGaloisIntermediateField.subset_adjoin F (s : Set Ω)
    obtain ⟨τ, hτ⟩ := GlobalTheory.KZ.ES.exists_conj_of_same_trace F L (A.comap (algebraMap L Ω))
      (B.comap (algebraMap L Ω)) (by
        intro a
        rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
          ← IsScalarTower.algebraMap_apply]
        exact h a)
    refine ⟨τ.liftNormal Ω, fun x hx => ?_⟩
    have hxL : x ∈ L := hsL hx
    have key := hτ ⟨x, hxL⟩
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at key
    have he : (τ.liftNormal Ω) x = algebraMap L Ω (τ ⟨x, hxL⟩) :=
      AlgEquiv.liftNormal_commutes τ Ω ⟨x, hxL⟩
    rw [he]
    exact key
  have hdir : Directed (fun s t => s ⊇ t) C := by
    intro s t
    exact ⟨s ∪ t, fun σ hσ x hx => hσ x (Finset.mem_union_left _ hx),
      fun σ hσ x hx => hσ x (Finset.mem_union_right _ hx)⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun s => (hclosed s).isCompact) hclosed
  refine ⟨σ, fun x => ?_⟩
  exact Set.mem_iInter.mp hσ {x} x (Finset.mem_singleton_self x)

theorem exists_conj_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  intro Ω _ _ _ p _ A B hA hB
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hA' := (A.mem_nonunits_iff).mp hA
  have hB' := (B.mem_nonunits_iff).mp hB
  apply exists_conj_of_isGalois A B
  intro a
  rw [eq_ratCast, ratCast_mem_iff hp A hA', ratCast_mem_iff hp B hB']

end GlobalTheory.ValConjClosure
