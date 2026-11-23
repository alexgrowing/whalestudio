import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
open GlobalTheory.GLq Polynomial
open scoped Classical

namespace GlobalTheory.AbsIrrDescent

theorem isSimpleModule_of_finrank_end {k R M : Type} [Field k] [Ring R] [Algebra k R] [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [SMulCommClass R k M] [IsSemisimpleModule R M]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

theorem isIrreducible_of_norm_one {k G V : Type} [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (hn : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  have hc : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have : NeZero (Nat.card G : k) := ⟨hc⟩
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hn, inv_mul_cancel₀ hc, eq_comm, Nat.cast_eq_one] at h
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine isSimpleModule_of_finrank_end (k := k) ?_
  rw [← h]
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq.symm

theorem isAbsIrrChar_of_isIrr : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (χ : G → K), IsIrr (fun t => σ (χ t)) → Formalism.L2.DIV.IsAbsIrrChar χ := by
  intro K _ σ G _ _ χ h
  obtain ⟨V, hV, hχ⟩ := h
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  let τ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) ℂ := τ.toRingHom.toAlgebra
  have hτ : ∀ x : K, algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) x) = σ x :=
    fun x => τ.commutes x
  have hinj : Function.Injective (algebraMap (AlgebraicClosure K) ℂ) := RingHom.injective _
  have hm : Nat.card G ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card G) := ⟨hm⟩
  haveI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.2 hm⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (Nat.card G)
  have hch : GlobalTheory.BI.IsChar ℂ ℂ (fun t => σ (χ t)) := by
    have h := (GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G V V.ρ).1
    have e : (fun t => σ (χ t)) = fun g => algebraMap ℂ ℂ (Representation.character V.ρ g) := by
      funext g
      exact (hχ g).symm
    rw [e]
    exact h
  obtain ⟨n, ρ, hρ⟩ := GlobalTheory.BI.isChar_of_isPrimitiveRoot (AlgebraicClosure K) ℂ (Nat.card G) ζ hm hζ G
    (fun g => pow_card_eq_one') _ hch
  have hρ' : ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t) := fun t =>
    hinj (by rw [hτ]; exact (hρ t).symm)
  refine ⟨n, ρ, isIrreducible_of_norm_one ρ (hinj ?_), hρ'⟩
  have hn := (FDRep.simple_iff_char_is_norm_one V).1 hV
  rw [map_natCast, ← hn, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, hρ', hρ', hτ, hτ, hχ, hχ]

end GlobalTheory.AbsIrrDescent
