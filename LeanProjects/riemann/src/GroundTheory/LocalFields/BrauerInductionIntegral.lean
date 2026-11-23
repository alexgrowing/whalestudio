import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section OneDim

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem eq_trace_smul_id_of_finrank_eq_one (h : finrank ℂ V = 1) (f : V →ₗ[ℂ] V) :
    f = LinearMap.trace ℂ V f • LinearMap.id := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ h
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (by omega)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h (f v)
  have hf : f = c • LinearMap.id := by
    ext w
    obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h w
    simp [map_smul, ← hc]
  rw [hf, map_smul, LinearMap.trace_id, h]
  simp

end OneDim

section Comm

variable {G : Type*} [Group G] [IsMulCommutative G]

theorem IsIrrCharacter.exists_monoidHom {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ l : G →* ℂˣ, ∀ g, χ g = l g := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := h
  have h1 : finrank ℂ V = 1 := IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have hmul : ∀ g k, ρ.character (g * k) = ρ.character g * ρ.character k := by
    intro g k
    have hg := eq_trace_smul_id_of_finrank_eq_one h1 (ρ g)
    have hk := eq_trace_smul_id_of_finrank_eq_one h1 (ρ k)
    simp only [Representation.character, map_mul]
    conv_lhs => rw [hg, hk]
    rw [smul_mul_smul, map_smul, Module.End.mul_eq_comp, LinearMap.id_comp, LinearMap.trace_id, h1]
    simp
  let f : G →* ℂ :=
    { toFun := ρ.character
      map_one' := by rw [char_one, h1]; simp
      map_mul' := hmul }
  exact ⟨f.toHomUnits, fun g ↦ rfl⟩

end Comm

section Values

variable {G : Type*} [Group G] [Fintype G]

theorem IsCharacter.exists_sum_zpow {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) :
    ∃ (m : (Subgroup.zpowers s → ℂ) → ℕ) (β : (Subgroup.zpowers s → ℂ) → ℂ),
      (∀ ψ, β ψ ^ orderOf s = 1) ∧
        ∀ a : ℤ, χ (s ^ a) = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ ^ a := by
  classical
  set C := Subgroup.zpowers s
  obtain ⟨m, hm⟩ := (hχ.comp C.subtype).exists_nat
  have hl : ∀ ψ ∈ irrChars C, ∃ l : C →* ℂˣ, ∀ c, ψ c = l c := fun ψ hψ ↦
    (mem_irrChars.mp hψ).exists_monoidHom
  choose! l hl using hl
  let s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  refine ⟨m, fun ψ ↦ if ψ ∈ irrChars C then (l ψ s' : ℂ) else 1, fun ψ ↦ ?_, fun a ↦ ?_⟩
  · dsimp only
    split_ifs
    · rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have : s' ^ orderOf s = 1 := by
        ext
        simp [s', pow_orderOf_eq_one]
      rw [this, map_one, Units.val_one]
    · exact one_pow _
  · have h := congrFun hm (s' ^ a)
    simp only [Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_zpow, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    refine Finset.sum_congr rfl fun ψ hψ ↦ ?_
    dsimp only
    rw [if_pos hψ, hl ψ hψ, map_zpow, Units.val_zpow_eq_zpow_val]

theorem IsCharacter.apply_mem_adjoin {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {N : ℕ} [NeZero N]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : orderOf s ∣ N) :
    χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  obtain ⟨m, β, hβ, h⟩ := hχ.exists_sum_zpow s
  have hβN : ∀ ψ, β ψ ^ N = 1 := by
    intro ψ
    obtain ⟨k, hk⟩ := hN
    rw [hk, pow_mul, hβ, one_pow]
  have hmem : ∀ ψ, β ψ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
    intro ψ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hβN ψ)
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have h1 : χ s = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ := by
    simpa using h 1
  rw [h1]
  exact Subalgebra.sum_mem _ fun ψ _ ↦ Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem ψ)

theorem IsCharacter.apply_mem_adjoin_card {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Nat.card G)) : χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact hχ.apply_mem_adjoin s hζ (orderOf_dvd_natCard s)

end Values

section Retraction

theorem exists_retraction_adjoin {ζ : ℂ} (hζ : IsIntegral ℤ ζ) :
    ∃ π : Algebra.adjoin ℤ ({ζ} : Set ℂ) →ₗ[ℤ] ℤ, π 1 = 1 := by
  let pb := Algebra.adjoin.powerBasis' hζ
  have hdim : 0 < pb.dim := pb.dim_pos
  refine ⟨pb.basis.coord ⟨0, hdim⟩, ?_⟩
  have h0 : pb.basis ⟨0, hdim⟩ = 1 := by
    rw [pb.coe_basis]
    simp
  rw [← h0, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

theorem exists_int_of_mul_eq_int {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {a : ℂ}
    (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {d k : ℤ} (hd : d ≠ 0) (h : (d : ℂ) * a = k) :
    ∃ z : ℤ, a = z ∧ d * z = k := by
  obtain ⟨π, hπ⟩ := exists_retraction_adjoin hζ
  let a' : Algebra.adjoin ℤ ({ζ} : Set ℂ) := ⟨a, ha⟩
  have h' : d • a' = k • (1 : Algebra.adjoin ℤ ({ζ} : Set ℂ)) := by
    apply Subtype.ext
    simp [a', h]
  have h'' := congrArg π h'
  rw [map_zsmul, map_zsmul, hπ, smul_eq_mul, smul_eq_mul, mul_one] at h''
  refine ⟨π a', ?_, h''⟩
  have hd' : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd
  apply mul_left_cancel₀ hd'
  rw [h, ← h'']
  push_cast
  ring

end Retraction

section Frobenius

variable {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
include hp

theorem exists_sum_pow_prime_pow_eq {ι : Type*} (s : Finset ι) (b : ι → R) (n : ℕ) :
    ∃ r : R, (∑ i ∈ s, b i) ^ p ^ n = ∑ i ∈ s, b i ^ p ^ n + p * r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (b a) (∑ i ∈ s, b i) n
    refine ⟨r + b a * (∑ i ∈ s, b i) * r', ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring

end Frobenius

end GroundTheory.LocalField
