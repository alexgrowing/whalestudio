import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.PolAct

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def homF (A : Submodule R M) (w : ℕ) : Submodule R ((Fin 2 → R) → M) where
  carrier := {b | ∃ c : Fin (w + 1) → M, (∀ i, c i ∈ A) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}
  zero_mem' := ⟨0, fun _ => A.zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c + d, fun i => A.add_mem (hc i) (hd i), fun u => by
      simp [ha, hb, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro r b ⟨c, hc, hb⟩
    exact ⟨r • c, fun i => A.smul_mem r (hc i), fun u => by
      simp only [Pi.smul_apply, hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma const_mem_homF_zero {A : Submodule R M} {x : M} (hx : x ∈ A) :
    (fun _ : Fin 2 → R => x) ∈ _root_.GlobalTheory.KZ.PolAct.homF A 0 :=
  ⟨fun _ => x, fun _ => hx, fun u => by simp⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_zero_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 0 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨Fin.cons 0 c, fun i => ?_, fun u => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [A.zero_mem]
    · simp [hc]
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, zero_add, Fin.val_succ,
      Nat.add_sub_add_right, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_one_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 1 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨fun j => if h : (j : ℕ) < n + 1 then c ⟨j, h⟩ else 0, fun j => ?_, fun u => ?_⟩
  · dsimp only
    split_ifs
    · exact hc _
    · exact A.zero_mem
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_self_iff_false,
      dif_neg, not_false_eq_true, smul_zero, add_zero, Fin.eta, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : n + 1 - (i : ℕ) = n - (i : ℕ) + 1 := Nat.sub_add_comm (Nat.lt_succ_iff.mp i.isLt)
    rw [hi, pow_succ]
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    (fun u => (α * u 0 + β * u 1) • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  have h := (_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).add_mem
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem α
      (coord_zero_smul_mem_homF_succ hb))
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem β
      (coord_one_smul_mem_homF_succ hb))
  convert h using 1
  funext u
  simp [add_smul, mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_pow_smul_mem_homF_add {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    ∀ k : ℕ, (fun u => (α * u 0 + β * u 1) ^ k • b u) ∈
      _root_.GlobalTheory.KZ.PolAct.homF A (n + k) := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := linear_form_smul_mem_homF_succ ih α β
    show _ ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + k + 1)
    convert h using 1
    funext u
    simp only [pow_succ', mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.PolAct.subst_mem {A : Submodule R M} {w : ℕ} (φ : M →ₗ[R] M)
    (hφ : ∀ a ∈ A, φ a ∈ A)
    (m : Matrix (Fin 2) (Fin 2) R) {b : (Fin 2 → R) → M}
    (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A w) :
    (fun u => φ (b (m *ᵥ u))) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
  obtain ⟨c, hc, hbu⟩ := hb
  have hterm : ∀ i : Fin (w + 1), (fun u : Fin 2 → R =>
      ((m 0 0 * u 0 + m 0 1 * u 1) ^ (i : ℕ) * (m 1 0 * u 0 + m 1 1 * u 1) ^ (w - (i : ℕ))) •
        φ (c i)) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
    intro i
    have h0 := const_mem_homF_zero (hφ _ (hc i))
    have h1 := linear_form_pow_smul_mem_homF_add h0 (m 1 0) (m 1 1) (w - i)
    have h2 := linear_form_pow_smul_mem_homF_add h1 (m 0 0) (m 0 1) i
    have hdeg : 0 + (w - (i : ℕ)) + i = w := by
      have := i.isLt
      omega
    rw [hdeg] at h2
    convert h2 using 1
    funext u
    simp only [mul_smul]
  have hsum := Submodule.sum_mem (_root_.GlobalTheory.KZ.PolAct.homF A w)
    (t := Finset.univ) (fun i _ => hterm i)
  convert hsum using 1
  funext u
  simp [hbu, map_sum, map_smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Finset.sum_apply]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.PolAct.act_mem_pol {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l w : ℕ) [Fact l.Prime]
    (m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ a ∈ X.A l, X.kmap l
      (X.sl (_root_.GlobalTheory.KZ.toGQ m)).toRingEquiv a ∈ X.A l) :
    ∀ b ∈ X.Pol l w,
      X.act l m b ∈
        X.Pol l w := by
  intro b hb
  exact _root_.GlobalTheory.KZ.PolAct.subst_mem (A := X.A l) (w := w) _ h _ hb

end GlobalTheory.KZ.PolAct
