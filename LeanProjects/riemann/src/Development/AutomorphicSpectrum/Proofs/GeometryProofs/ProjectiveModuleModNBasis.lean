import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.ModFree

open NumberField Module
open scoped nonZeroDivisors TensorProduct

theorem exists_map_of_basis {O B M Mb : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    (S : Submonoid O) (hS : S ≤ O⁰) [IsLocalization S B] [AddCommGroup M] [Module O M]
    [AddCommGroup Mb] [Module O Mb] [Module B Mb] [IsScalarTower O B Mb] (f : M →ₗ[O] Mb)
    [IsLocalizedModule S f] {n : ℕ} (b : Basis (Fin n) B Mb) :
    ∃ φ : (Fin n → O) →ₗ[O] M, Function.Injective φ ∧
      ∀ m, ∃ s : S, ∃ y, (s : O) • m = φ y := by
  choose p hp using fun i => IsLocalizedModule.surj S f (b i)
  have hinj : Function.Injective (algebraMap O B) := IsLocalization.injective B hS
  refine ⟨Fintype.linearCombination O (fun i => (p i).1), ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [Fintype.linearCombination_apply] at hy
    have h1 : ∑ i, algebraMap O B (y i * (p i).2) • b i = 0 := by
      have h := congrArg f hy
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, algebraMap_smul, mul_smul]
    have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h1
    funext i
    have h3 : y i * (p i).2 = 0 := hinj (by rw [h2 i, map_zero])
    exact (mul_eq_zero.mp h3).resolve_right (nonZeroDivisors.ne_zero (hS (p i).2.2))
  · intro x
    have hx := b.sum_repr (f x)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ
      (fun i => b.repr (f x) i * ((IsLocalization.map_units B (p i).2).unit⁻¹ : Bˣ))
    choose a ha using fun i => RingHom.mem_rangeS.mp (ht i (Finset.mem_univ i))
    have hc : ∀ i, algebraMap O B (a i) * algebraMap O B (p i).2 =
        algebraMap O B t * b.repr (f x) i := by
      intro i
      rw [ha i, Algebra.smul_def, mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have key : f ((t : O) • x) = f (Fintype.linearCombination O (fun i => (p i).1) a) := by
      rw [map_smul, Fintype.linearCombination_apply, map_sum, ← hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, ← algebraMap_smul B (a i),
        ← algebraMap_smul B ((p i).2 : O), smul_smul, hc i, mul_smul, algebraMap_smul]
    obtain ⟨c, hc'⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) key
    refine ⟨c * t, (c : O) • a, ?_⟩
    rw [map_smul, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, hc', Submonoid.smul_def]

theorem exists_free_map_mod (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M →
    ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N →
    ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧
      ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  intro hfin hproj n N hn hN
  set S := GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N with hSdef
  have hS : S ≤ (𝓞 E)⁰ := by
    rintro s ⟨k, hk0, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hk0)
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  have : IsPrincipalIdealRing (Localization S) :=
    GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS (Localization S)
  have hrank : Module.finrank (Localization S) (LocalizedModule S M) = n := by
    rw [IsLocalization.finrank_eq (Localization S) S hS,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hS, hn]
  let b := Module.finBasisOfFinrankEq (Localization S) (LocalizedModule S M) hrank
  obtain ⟨φ, hφ, hsurj⟩ := exists_map_of_basis S hS (LocalizedModule.mkLinearMap S M) b
  have hunit : ∀ s : S, ∃ k : ℕ, (s : 𝓞 E) = k ∧ ∃ u v : ℤ, u * k + v * N = 1 := by
    rintro ⟨_, k, -, hkc, rfl⟩
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hkc
    exact ⟨k, rfl, u, v, huv⟩
  refine ⟨φ, fun m => ?_, fun x c hxc => ?_⟩
  · obtain ⟨s, y, hs⟩ := hsurj m
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    refine ⟨u • y, v • m, ?_⟩
    calc m = ((u * k + v * N : ℤ)) • m := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • m) + (N : ℤ) • (v • m) := by
        rw [add_smul, mul_smul, mul_comm v, mul_smul]
      _ = φ (u • y) + N • (v • m) := by
        rw [map_zsmul, ← hs, natCast_zsmul, natCast_zsmul]
  · obtain ⟨s, y, hs⟩ := hsurj c
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    have hNy : N • y = k • x := by
      apply hφ
      rw [map_nsmul, map_nsmul, ← hs, hxc, smul_comm]
    refine ⟨u • y + v • x, ?_⟩
    calc x = ((u * k + v * N : ℤ)) • x := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • x) + v • ((N : ℤ) • x) := by
        rw [add_smul, mul_smul, mul_smul]
      _ = N • (u • y + v • x) := by
        rw [natCast_zsmul, natCast_zsmul, ← hNy, smul_add, smul_comm u N y, smul_comm v N x]

end GlobalTheory.CompanionTheory.ModFree
