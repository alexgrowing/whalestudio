import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.Equivariance

lemma mul_prod_ofFn {A ι : Type} [Ring A] [Algebra ℂ A] [Fintype ι] (X : ι → A) (z : A) (c : ι → ι → ℂ)
    (h : ∀ x, z * X x = X x * z + ∑ y, c y x • X y) (k : ℕ) (g : Fin k → ι) :
    z * (List.ofFn fun i => X (g i)).prod = (List.ofFn fun i => X (g i)).prod * z +
      ∑ i, ∑ y, c y (g i) • (List.ofFn fun j => X (Function.update g i y j)).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ (i : Fin k) (y : ι) (j : Fin k), Function.update g i.succ y j.succ =
        Function.update (fun j : Fin k => g j.succ) i y j := by
      intro i y j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, Function.update_of_ne (fun h' => hj (Fin.succ_injective _ h'))]
    have e0 : ∀ (y : ι) (j : Fin k), Function.update g 0 y j.succ = g j.succ := fun y j =>
      Function.update_of_ne (Fin.succ_ne_zero j) _ _
    have e1 : ∀ (i : Fin k) (y : ι), Function.update g i.succ y 0 = g 0 := fun i y =>
      Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, e, e0, e1, Function.update_self]
    rw [← mul_assoc, h, add_mul, mul_assoc, ih (fun j => g j.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

variable {R S : ℕ}

lemma bracket_eNC {Z : Mat R S} (hZ : IsKC Z) (x : NC R S) :
    Z * eNC x - eNC x * Z = ∑ y, adP Z y x • eNC y := by
  obtain ⟨⟨a, b⟩, hab⟩ := x
  ext c d
  have hab' : ¬ sameBlock a b := hab
  have hl : (Z * eNC ⟨(a, b), hab⟩ - eNC ⟨(a, b), hab⟩ * Z) c d =
      Z c a * (if d = b then 1 else 0) - (if c = a then 1 else 0) * Z b d := by
    simp only [eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
    congr 1
    · by_cases h : d = b
      · subst h; simp
      · simp [h, Ne.symm h]
    · by_cases h : c = a
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [hl, Matrix.sum_apply]
  by_cases hcd : sameBlock c d
  · rw [Finset.sum_eq_zero]
    · have h1 : Z c a * (if d = b then 1 else 0) = 0 := by
        by_cases h : d = b
        · subst h
          rw [hZ c a, zero_mul]
          clear hl hab
          rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
        · simp [h]
      have h2 : (if c = a then 1 else 0) * Z b d = 0 := by
        by_cases h : c = a
        · subst h
          rw [hZ b d, mul_zero]
          clear h1 hl hab
          rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
        · simp [h]
      rw [h1, h2, sub_zero]
    · rintro ⟨⟨u, v⟩, huv⟩ _
      have : ¬ (u = c ∧ v = d) := by
        rintro ⟨rfl, rfl⟩
        exact huv hcd
      simp [eNC, Eab, Matrix.single_apply, this]
  · rw [Finset.sum_eq_single (⟨(c, d), hcd⟩ : NC R S)]
    · simp [eNC, Eab, adP]
    · rintro ⟨⟨u, v⟩, huv⟩ _ hne
      have : ¬ (u = c ∧ v = d) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp [eNC, Eab, Matrix.single_apply, this]
    · simp

lemma sum_update_swap {ι B : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid B] {k : ℕ} (i : Fin k)
    (F : (Fin k → ι) → (Fin k → ι) → ι → ι → B) :
    ∑ g, ∑ x, F g (Function.update g i x) (g i) x = ∑ g, ∑ y, F (Function.update g i y) g y (g i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun p => (Function.update p.1 i p.2, p.1 i))
    (fun p => (Function.update p.1 i p.2, p.1 i)) ?_ ?_ ?_ ?_ ?_ <;> simp

theorem phiN_tAct : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V) (hN : KStable M.act N) (k : ℕ) (Z : Mat R S),
    IsKC Z → ∀ Ψ : (Fin k → NC R S) → N,
      phiN M.act N k (tAct k (restrAct M.act N hN) Z Ψ) = M.act Z (phiN M.act N k Ψ) := by
  intro R S M N hN k Z hZ Ψ
  have h : ∀ x : NC R S, M.act Z * M.act (eNC x) =
      M.act (eNC x) * M.act Z + ∑ y, adP Z y x • M.act (eNC y) := by
    intro x
    have h1 := M.lie Z (eNC x)
    rw [bracket_eNC hZ, map_sum] at h1
    simp only [map_smul] at h1
    rw [h1]; abel
  have hw : ∀ (g : Fin k → NC R S) (v : M.V), M.act Z (word M.act g v) = word M.act g (M.act Z v) +
      ∑ i, ∑ y, adP Z y (g i) • word M.act (Function.update g i y) v := by
    intro g v
    have := congrArg (fun T : Module.End ℂ M.V => T v)
      (mul_prod_ofFn (fun x => M.act (eNC x)) (M.act Z) (adP Z) h k g)
    simpa [word, LinearMap.sum_apply] using this
  simp only [phiN_apply, tAct_apply, map_sum, hw, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    restrAct_apply, kpart_of_isKC hZ, map_add, map_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_update_swap i (fun g g' y x => adP Z y x • word M.act g (Ψ g' : M.V))

end GlobalTheory.SteepMult.Equivariance
