import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormBilinFormsEqSumMinimiserValues
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

theorem symm_bilin_pow_dvd_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    ∀ k : ℕ, ∀ x y, (N : ℤ) ^ k ∣ B x y := by
  have hdec : ∀ x : Y, ∃ y : Y, x = μ (fun i => (eb x i : ZMod N)) + (N : ℤ) • y := by
    intro x
    have hd : ∀ i, (N : ℤ) ∣ eb x i - eb (μ (fun i => (eb x i : ZMod N))) i := by
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hμ _ i, sub_self]
    choose z hz using hd
    refine ⟨eb.symm z, ?_⟩
    apply eb.injective
    funext i
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hz i]
  have hdiag : ∀ k, (∀ x y, (N : ℤ) ^ k ∣ B x y) → ∀ x, (N : ℤ) ^ (k + 1) ∣ B x x := by
    intro k hk x
    obtain ⟨y, hy⟩ := hdec x
    have hm := h0 (fun i => (eb x i : ZMod N))
    generalize μ (fun i => (eb x i : ZMod N)) = m at hy hm
    subst hy
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hm]
    rw [hB y m]
    obtain ⟨a, ha⟩ := hk m y
    obtain ⟨b, hb⟩ := hk y y
    rw [ha, hb]
    exact ⟨2 * a + N * b, by ring⟩
  have hcop : IsCoprime (N : ℤ) 2 := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_right.mpr hodd)
    exact_mod_cast this
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    have h2 : (N : ℤ) ^ (k + 1) ∣ 2 * B x y := by
      have hxy := hdiag k ih (x + y)
      have hx := hdiag k ih x
      have hy := hdiag k ih y
      have e : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
        simp only [map_add, LinearMap.add_apply]
        rw [hB y x]
        ring
      rw [e]
      exact dvd_sub (dvd_sub hxy hx) hy
    exact (hcop.pow_left).dvd_of_dvd_mul_left h2

theorem symm_bilin_eq_zero_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    B = 0 := by
  ext x y
  have h := symm_bilin_pow_dvd_of_lifts n N hodd eb μ hμ B hB h0 (B x y).natAbs x y
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem linForm_eq_sum_lifts : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  intro Y _ n N _ hN hodd eb μ hμ ℓ
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let S : Submodule ℤ (LinearMap.BilinForm ℤ Y) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ((Fin n → ZMod N) → ℤ) :=
    { toFun := fun b c => b (μ c) (μ c)
      map_add' := by intro a b; funext c; simp
      map_smul' := by intro k b; funext c; simp }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    refine symm_bilin_eq_zero_of_lifts n N hN hodd eb μ hμ _ ?_ ?_
    · intro u v
      simp [x.2 u v, y.2 u v]
    · intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp [this]
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
