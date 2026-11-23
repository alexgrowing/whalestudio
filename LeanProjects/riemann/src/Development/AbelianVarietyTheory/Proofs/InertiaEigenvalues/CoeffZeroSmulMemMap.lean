import Mathlib

namespace GlobalTheory.CoefficientMembership

theorem aeval_mem {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V)
    (Z : Submodule O V) (hZ : ∀ z ∈ Z, T z ∈ Z) (q : Polynomial O) :
    ∀ w ∈ Z, (Polynomial.aeval T q) w ∈ Z := by
  intro w hw
  have hpow : ∀ k : ℕ, (T ^ k) w ∈ Z := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hZ _ ih
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact Z.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Z.smul_mem a (hpow n)

theorem coeff_zero_smul_mem_map : ∀ {O V : Type} [inst : CommRing O] [inst_1 : AddCommGroup V] [inst_2 : Module O V] (T : Module.End O V) (Rp : Polynomial O), (Polynomial.aeval T : Polynomial O → Module.End O V) Rp * T = (0 : Module.End O V) → ∀ (Z : Submodule O V), (∀ z ∈ Z, (T : V → V) z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → Polynomial.coeff Rp (0 : ℕ) • w ∈ Submodule.map T Z := by
  intro O V _ _ _ T Rp hR Z hZ w hw hwr
  obtain ⟨v, rfl⟩ := hwr
  have key : (Polynomial.aeval T Rp) (T v) =
      T ((Polynomial.aeval T Rp.divX) (T v)) + Rp.coeff 0 • T v := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Rp]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply]
  have h0 : (Polynomial.aeval T Rp) (T v) = 0 := by
    have := congrArg (fun f : Module.End O V => f v) hR
    simpa using this
  rw [h0] at key
  refine Submodule.mem_map.mpr ⟨-(Polynomial.aeval T Rp.divX) (T v),
    Z.neg_mem (aeval_mem T Z hZ _ _ hw), ?_⟩
  rw [map_neg]
  exact neg_eq_of_add_eq_zero_right key.symm

end GlobalTheory.CoefficientMembership
