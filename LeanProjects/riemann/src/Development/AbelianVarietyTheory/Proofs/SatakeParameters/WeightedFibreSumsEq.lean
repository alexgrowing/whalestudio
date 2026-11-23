import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory
namespace OrbitDoubleCount

def transporterEquiv {Γ Y : Type} [Group Γ] [MulAction Γ Y] (v : Y) (δ : Γ) :
    {γ : Γ // γ • (δ • v) = v} ≃ MulAction.stabilizer Γ v where
  toFun γ := ⟨γ.1 * δ, by rw [MulAction.mem_stabilizer_iff, mul_smul]; exact γ.2⟩
  invFun s := ⟨s.1 * δ⁻¹, by
    rw [mul_smul, inv_smul_smul]; exact MulAction.mem_stabilizer_iff.mp s.2⟩
  left_inv γ := by ext; simp
  right_inv s := by ext; simp

theorem transporter_isEmpty {Γ Y : Type} [Group Γ] [MulAction Γ Y] (u v : Y)
    (h : u ∉ MulAction.orbit Γ v) : IsEmpty {γ : Γ // γ • u = v} :=
  ⟨fun γ => h ⟨γ.1⁻¹, by
    show γ.1⁻¹ • v = u
    rw [inv_smul_eq_iff]; exact γ.2.symm⟩⟩

theorem transporter_finite {Γ Y : Type} [Group Γ] [MulAction Γ Y] (u v : Y)
    [Finite (MulAction.stabilizer Γ v)] : Finite {γ : Γ // γ • u = v} := by
  by_cases h : u ∈ MulAction.orbit Γ v
  · obtain ⟨δ, rfl⟩ := h
    exact Finite.of_equiv _ (transporterEquiv v δ).symm
  · haveI := transporter_isEmpty u v h
    infer_instance

theorem sum_transporter {Γ Y I' : Type} [Group Γ] [MulAction Γ Y] [Fintype I'] (y : I' → Y)
    (hy : ∀ u : Y, ∃! i, u ∈ MulAction.orbit Γ (y i))
    (hf : ∀ i, Finite (MulAction.stabilizer Γ (y i))) (u : Y) :
    ∑ j, ((Nat.card (MulAction.stabilizer Γ (y j)) : ℂ))⁻¹ *
      (Nat.card {γ : Γ // γ • u = y j} : ℂ) = 1 := by
  obtain ⟨j, hj, huniq⟩ := hy u
  rw [Finset.sum_eq_single j]
  · obtain ⟨δ, rfl⟩ := hj
    haveI := hf j
    have h1 : Nat.card {γ : Γ // γ • (δ • y j) = y j} = Nat.card (MulAction.stabilizer Γ (y j)) :=
      Nat.card_congr (transporterEquiv (y j) δ)
    have h2 : (Nat.card (MulAction.stabilizer Γ (y j)) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer Γ (y j))).ne'
    show _ * (Nat.card {γ : Γ // γ • (δ • y j) = y j} : ℂ) = 1
    rw [h1, inv_mul_cancel₀ h2]
  · intro k _ hk
    haveI := transporter_isEmpty (Γ := Γ) u (y k) (fun h => hk (huniq k h))
    simp
  · simp

def pairEquiv {Γ X Y Z : Type} [Group Γ] [MulAction Γ Y] (p : Z → X) (q : Z → Y) (x₀ : X) (y₀ : Y) :
    (Σ z : {z | p z = x₀}, {γ : Γ // γ • q z.1 = y₀}) ≃
      {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y₀} where
  toFun s := ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
  invFun t := ⟨⟨t.1.1, t.2.1⟩, ⟨t.1.2, t.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fibre_sum {Γ X Y Z I' : Type} [Group Γ] [MulAction Γ Y] [Fintype I']
    (p : Z → X) (q : Z → Y) (x₀ : X) (y : I' → Y) (φ : Z → ℂ)
    (hy : ∀ u : Y, ∃! i, u ∈ MulAction.orbit Γ (y i))
    (hf : ∀ i, Finite (MulAction.stabilizer Γ (y i))) (hx : {z | p z = x₀}.Finite) :
    ∑ᶠ z ∈ {z | p z = x₀}, φ z = ∑ j, ((Nat.card (MulAction.stabilizer Γ (y j)) : ℂ))⁻¹ *
      ∑ᶠ t : {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y j}, φ t.1.1 := by
  haveI : Fintype {z | p z = x₀} := hx.fintype
  have key : ∀ j, ∑ᶠ t : {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y j}, φ t.1.1 =
      ∑ z : {z | p z = x₀}, (Nat.card {γ : Γ // γ • q z.1 = y j} : ℂ) * φ z.1 := by
    intro j
    haveI := hf j
    haveI : ∀ z : {z | p z = x₀}, Fintype {γ : Γ // γ • q z.1 = y j} := fun z =>
      @Fintype.ofFinite _ (transporter_finite _ _)
    rw [← finsum_comp_equiv (pairEquiv p q x₀ (y j)), finsum_eq_sum_of_fintype, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun z _ => ?_
    show ∑ _γ : {γ : Γ // γ • q z.1 = y j}, φ z.1 = _
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, sum_transporter y hy hf, one_mul]

def swapEquiv {Γ X Y Z : Type} [Group Γ] [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]
    (p : Z → X) (q : Z → Y) (hp : ∀ (γ : Γ) z, p (γ • z) = γ • p z)
    (hq : ∀ (γ : Γ) z, q (γ • z) = γ • q z) (x₀ : X) (y₀ : Y) :
    {t : Z × Γ // p t.1 = x₀ ∧ t.2 • q t.1 = y₀} ≃ {t : Z × Γ // q t.1 = y₀ ∧ t.2 • p t.1 = x₀} where
  toFun t := ⟨(t.1.2 • t.1.1, t.1.2⁻¹), by rw [hq]; exact t.2.2, by
    show t.1.2⁻¹ • p (t.1.2 • t.1.1) = x₀
    rw [hp, inv_smul_smul]; exact t.2.1⟩
  invFun t := ⟨(t.1.2 • t.1.1, t.1.2⁻¹), by rw [hp]; exact t.2.2, by
    show t.1.2⁻¹ • q (t.1.2 • t.1.1) = y₀
    rw [hq, inv_smul_smul]; exact t.2.1⟩
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

end OrbitDoubleCount

open OrbitDoubleCount in

theorem weighted_fibre_sums_eq : ∀ {Γ X Y Z I I' : Type} [Group Γ] [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z] [Fintype I] [Fintype I'] (p : Z → X) (q : Z → Y) (x : I → X) (y : I' → Y) (φ : Z → ℂ), (∀ (γ : Γ) z, p (γ • z) = γ • p z) → (∀ (γ : Γ) z, q (γ • z) = γ • q z) → (∀ u : X, ∃! i, u ∈ MulAction.orbit Γ (x i)) → (∀ u : Y, ∃! i, u ∈ MulAction.orbit Γ (y i)) → (∀ i, Finite (MulAction.stabilizer Γ (x i))) → (∀ i, Finite (MulAction.stabilizer Γ (y i))) → (∀ i, {z | p z = x i}.Finite) → (∀ i, {z | q z = y i}.Finite) → (∀ (γ : Γ) z, φ (γ • z) = φ z) → ∑ i, ((Nat.card (MulAction.stabilizer Γ (x i)) : ℂ))⁻¹ * ∑ᶠ z ∈ {z | p z = x i}, φ z = ∑ i, ((Nat.card (MulAction.stabilizer Γ (y i)) : ℂ))⁻¹ * ∑ᶠ z ∈ {z | q z = y i}, φ z := by
  intro Γ X Y Z I I' _ _ _ _ _ _ p q x y φ hp hq hx hy fx fy gx gy hφ
  have h1 := fun i => fibre_sum p q (x i) y φ hy fy (gx i)
  have h2 := fun j => fibre_sum q p (y j) x φ hx fx (gy j)
  simp_rw [h1, h2, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  congr 2
  rw [← finsum_comp_equiv (swapEquiv p q hp hq (x i) (y j))]
  exact finsum_congr fun t => (hφ _ _).symm

end GlobalTheory
