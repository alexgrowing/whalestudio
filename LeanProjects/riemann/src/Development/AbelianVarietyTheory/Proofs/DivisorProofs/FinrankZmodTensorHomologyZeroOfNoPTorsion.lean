import Mathlib
open CategoryTheory Limits

namespace GlobalTheory

theorem exists_torsion_eq_prime_smul_of_noPTorsion {M : Type*} [AddCommGroup M] (p : ℕ)
    [hp : Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) (t : M)
    (ht : t ∈ Submodule.torsion ℤ M) :
    ∃ s ∈ Submodule.torsion ℤ M, t = (p : ℤ) • s := by
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff t).1 ht
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  change a • t = 0 at hat
  set n := a.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.2 ha0
  have hnt : (n : ℤ) • t = 0 := by
    rcases Int.natAbs_eq a with h | h
    · rw [← h]; exact hat
    · have : a = -(n : ℤ) := h
      rw [this, neg_smul, neg_eq_zero] at hat; exact hat
  have hpow : ∀ k : ℕ, ∀ y : M, ((p : ℤ) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, mul_smul] at hy
      exact hM y (ih _ hy)
  set k := n.factorization p
  set m := n / p ^ k
  have hnm : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hmt : (m : ℤ) • t = 0 := by
    apply hpow k
    rw [← mul_smul]
    have : ((p : ℤ) ^ k * (m : ℤ)) = (n : ℤ) := by exact_mod_cast hnm
    rw [this, hnt]
  have hndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out hn0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd
  have hic : IsCoprime (p : ℤ) (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using hcop
  obtain ⟨u, v, huv⟩ := hic
  refine ⟨u • t, Submodule.smul_mem _ _ ht, ?_⟩
  calc t = ((u * p + v * m : ℤ)) • t := by rw [huv, one_smul]
    _ = (p : ℤ) • (u • t) := by
      rw [add_smul, mul_smul, mul_smul, hmt, smul_zero, add_zero, smul_comm]

theorem subsingleton_zmod_tensor_torsion {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    obtain ⟨s, hs, hts⟩ := exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2
    have : t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M) := Subtype.ext hts
    rw [this, ← TensorProduct.smul_tmul]
    have hc : (p : ℤ) • c = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hc, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem finrank_zmod_tensor_eq_finrank_of_noPTorsion (M : Type*) [AddCommGroup M] [inst : Module ℤ M]
    [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) = Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  set T := Submodule.torsion ℤ M
  haveI : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  haveI := subsingleton_zmod_tensor_torsion p hM
  let g := LinearMap.baseChange (ZMod p) T.mkQ
  have hg : ⇑g = ⇑(LinearMap.lTensor (ZMod p) T.mkQ) := LinearMap.baseChange_eq_ltensor _
  have hex := lTensor_exact (ZMod p) (LinearMap.exact_subtype_mkQ T) (Submodule.mkQ_surjective T)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : LinearMap.lTensor (ZMod p) T.mkQ y = 0 := by rw [← hg]; exact hy
    obtain ⟨z, rfl⟩ := (hex y).1 hy'
    rw [Subsingleton.elim z 0, map_zero]
  have hsurj : Function.Surjective g := by
    rw [hg]; exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective T)
  rw [(LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_baseChange,
    finrank_quotient_eq_of_le_torsion le_rfl]

theorem finrank_zmod_tensor_homology_zero :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) →
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) =
        Module.finrank ℤ (C.homology 0) := by
  intro C p _ hC _
  let f : C.homology 0 ⟶ C.X 0 := C.isoHomologyπ₀.inv ≫ C.iCycles 0
  have hinj : Function.Injective (ConcreteCategory.hom f) :=
    (ModuleCat.mono_iff_injective f).1 inferInstance
  apply finrank_zmod_tensor_eq_finrank_of_noPTorsion
  intro x hx
  apply hinj
  rw [map_zero]
  apply hC
  rw [← map_zsmul, hx, map_zero]

end GlobalTheory
