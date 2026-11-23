import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.ZModFlat

open scoped TensorProduct

theorem exists_mul_eq_zero_of_smul_eq_zero (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M]
    (hdiv : ∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y)
    (a : ULift.{1} (ZMod q)) (y : M) (hy : a • y = 0) :
    ∃ e : ℕ, (e : ULift.{1} (ZMod q)) * a = 0 ∧ ∃ z : M, y = e • z := by
  set n := a.down.val with hn
  have ha : a = (n : ULift.{1} (ZMod q)) := by
    apply ULift.down_injective
    rw [ULift.down_natCast, hn, ZMod.natCast_zmod_val]
  have hq : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simp
  have hgq : Nat.gcd n q ∣ q := Nat.gcd_dvd_right n q
  have hgn : Nat.gcd n q ∣ n := Nat.gcd_dvd_left n q
  refine ⟨q / Nat.gcd n q, ?_, ?_⟩
  · rw [ha, ← Nat.cast_mul]
    have : q ∣ q / Nat.gcd n q * n := by
      have h := Nat.mul_dvd_mul (dvd_refl (q / Nat.gcd n q)) hgn
      rwa [Nat.div_mul_cancel hgq] at h
    obtain ⟨m, hm⟩ := this
    rw [hm, Nat.cast_mul, hq, zero_mul]
  · apply hdiv (Nat.gcd n q) (q / Nat.gcd n q) (Nat.mul_div_cancel' hgq)
    have h1 : n • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← ha, hy]
    have h2 : q • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hq, zero_smul]
    have hb : ((Nat.gcd n q : ℕ) : ℤ) = n * Nat.gcdA n q + q * Nat.gcdB n q :=
      Nat.gcd_eq_gcd_ab n q
    have h3 : ((n : ℤ) * Nat.gcdA n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h1, smul_zero]
    have h4 : ((q : ℤ) * Nat.gcdB n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h2, smul_zero]
    rw [← natCast_zsmul, hb, add_smul, h3, h4, add_zero]

theorem flat_of_divisibility : ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M],
    (∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y) →
      Module.Flat (ULift.{1} (ZMod q)) M := by
  intro q _ M _ _ hdiv
  haveI : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective
      ((ULift.ringEquiv (R := ZMod q)).symm.toRingHom.comp (Int.castRingHom (ZMod q)))
      (by
        intro x
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.down
        exact ⟨z, by apply ULift.down_injective; simpa using hz⟩)
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal J).principal
  let b : J := ⟨a, by rw [ha]; exact Submodule.mem_span_singleton_self a⟩
  have hall : ∀ t : J ⊗[ULift.{1} (ZMod q)] M, ∃ y : M, t = b ⊗ₜ y := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r x =>
      have hr : (r : ULift.{1} (ZMod q)) ∈ Submodule.span (ULift.{1} (ZMod q)) {a} := ha ▸ r.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
      refine ⟨c • x, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      ext
      simp [b, ← hc]
    | add s t hs ht =>
      obtain ⟨y1, rfl⟩ := hs
      obtain ⟨y2, rfl⟩ := ht
      exact ⟨y1 + y2, (TensorProduct.tmul_add _ _ _).symm⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨y, rfl⟩ := hall t
  have hy : a • y = 0 := by
    have := congrArg (TensorProduct.lid (ULift.{1} (ZMod q)) M) ht
    simpa [b] using this
  obtain ⟨e, he, z, rfl⟩ := exists_mul_eq_zero_of_smul_eq_zero q M hdiv a y hy
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← TensorProduct.smul_tmul]
  have : ((e : ULift.{1} (ZMod q))) • b = 0 := by
    ext
    simp [b, he]
  rw [this, TensorProduct.zero_tmul]

end GlobalTheory.ZModFlat
