import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Scinv
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearcoord
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cntconj

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.nearvec :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    (nearVec A).Finite ∧ (nearVec A).ncard ≤ (2 * RR L N + 1) ^ dd L N := by
  intro L _ _ _ N A hA
  obtain ⟨hpos, B, hAB, _⟩ := scinv L N A hA
  obtain ⟨hSf, hSc⟩ := cntconj L (RR L N)
  let T : Finset (Fin N → 𝓞 L) := Fintype.piFinset fun _ => hSf.toFinset
  have hmaps : ∀ y ∈ nearVec A, (fun v : Fin N → 𝓞 L => B *ᵥ v) y ∈ (T : Set (Fin N → 𝓞 L)) := by
    intro y hy
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro a
    rw [Set.Finite.mem_toFinset]
    exact fun w => nearcoord L N A B hA hAB y hy w a
  have hc : ((nrmDet A : ℕ) : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hinj : Function.Injective (fun v : Fin N → 𝓞 L => B *ᵥ v) := by
    intro y y' h
    have h' := congrArg (fun v => A *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, hAB, Matrix.smul_mulVec, Matrix.one_mulVec] at h'
    exact smul_right_injective _ hc h'
  refine ⟨(T.finite_toSet.preimage hinj.injOn).subset hmaps, ?_⟩
  calc (nearVec A).ncard ≤ (T : Set (Fin N → 𝓞 L)).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj.injOn T.finite_toSet
    _ = hSf.toFinset.card ^ N := by
        rw [Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ ((2 * RR L N + 1) ^ Module.finrank ℚ L) ^ N := by
        apply Nat.pow_le_pow_left
        rw [← Set.ncard_eq_toFinset_card _ hSf]
        exact hSc
    _ = (2 * RR L N + 1) ^ dd L N := by rw [← pow_mul]
