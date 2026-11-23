import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeData

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz.CGlue

section Tens

variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]

theorem pm_apply' {M : Type} [AddCommGroup M] [Module ℂ M] (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) :
    pm σ f I = f (I ∘ σ) := rfl

theorem tE_diag_sum (S : Finset P) (f : TV n ℂ P) :
    ∑ i, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i i f = (S.card : ℂ) • f := by
  funext I
  simp [tE, lift, eAt, Finset.sum_apply]
  rw [Finset.sum_comm]
  have key : ∀ p, ∑ c : Fin n, (if I p = c then (LinearMap.proj (Function.update I p c) : TV n ℂ P →ₗ[ℂ] ℂ) else 0) f =
      ∑ c : Fin n, if I p = c then f I else 0 := by
    intro p
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  simp [key]

theorem cas_shift (S : Finset P) (s : ℂ) (f : TV n ℂ P) :
    ∑ i, ∑ j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j
        (tE S 0 j i f - if j = i then s • f else 0) - if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ P)) f -
        (2 * s * S.card - n * s ^ 2) • f := by
  have h1 : ∀ i j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j (tE S 0 j i f - if j = i then s • f else 0) -
      if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      tE S 0 i j (tE S 0 j i f) - if i = j then (s • tE S 0 i i f + s • tE S 0 i i f - (s * s) • f) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp only [if_true, map_sub, map_smul, smul_sub, smul_smul]; abel
    · rw [if_neg h, if_neg (Ne.symm h), if_neg h]; simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, tE_diag_sum]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

def colAnti {C : Type} (col : P → C) : Submodule ℂ (TV n ℂ P) where
  carrier := {f | ∀ p p', col p = col p' → p ≠ p' → pm (Equiv.swap p p') f = -f}
  add_mem' := fun {f g} hf hg p p' h1 h2 => by rw [map_add, hf p p' h1 h2, hg p p' h1 h2, neg_add]
  zero_mem' := fun p p' _ _ => by simp
  smul_mem' := fun c f hf p p' h1 h2 => by rw [map_smul, hf p p' h1 h2, smul_neg]

variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}

def tmap (Jh : Matrix (Fin d) (P → Fin n) ℂ) : TV n M P →ₗ[ℂ] M ⊗[ℂ] (Fin d → ℂ) :=
  ∑ I, (TensorProduct.mk ℂ M (Fin d → ℂ)).flip (fun m => Jh m I) ∘ₗ LinearMap.proj I

theorem tmap_apply (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) :
    tmap Jh f = ∑ I, f I ⊗ₜ (fun m => Jh m I) := by
  simp [tmap]

theorem actT_apply {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (γ : Γ) (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp [actT]

theorem tmap_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (Jh : Matrix (Fin d) (P → Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ)
    (h : Jh * Matrix.of (fun I J : P → Fin n => ∏ p, κ (lab p) γ (I p) (J p)) = B * Jh) (f : TV n M P) :
    tmap Jh (actT lab κ ρ γ f) = TensorProduct.map (ρ γ) (Matrix.toLin' B) (tmap Jh f) := by
  rw [tmap_apply, tmap_apply, map_sum]
  simp only [actT_apply, TensorProduct.sum_tmul, TensorProduct.smul_tmul, TensorProduct.map_tmul, Matrix.toLin'_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← TensorProduct.tmul_sum]
  congr 1
  funext m
  have := congrFun (congrFun h m) J
  simp only [Matrix.mul_apply, Matrix.of_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ← this]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

theorem tmap_ne (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) (lam : M →ₗ[ℂ] ℂ)
    (h : Jh *ᵥ (fun I => lam (f I)) ≠ 0) : tmap Jh f ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg (fun x => TensorProduct.lid ℂ (Fin d → ℂ) (lam.rTensor _ x)) h0
  simp only [tmap_apply, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h1
  funext m
  have h2 := congrFun h1 m
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

end Tens

theorem sum_fin_val (n : ℕ) : (∑ i : Fin n, ((i : ℕ) : ℝ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, add_mul]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem arith (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    (∑ i, (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n)) - (2 * s * ∑ i, (ν i : ℝ) - n * (s : ℝ) ^ 2) =
      ∑ k, (((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (k : ℕ)) ^ 2) := by
  have hl : ∀ i, (l (w i) : ℝ) = s - ν i - (i : ℕ) := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (h i)
    push_cast at this
    linarith
  have hm := sum_fin_val n
  rw [Finset.sum_sub_distrib, ← Equiv.sum_comp w (fun k => ((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2),
    ← Finset.sum_sub_distrib]
  simp only [hl]
  have e : ∀ i : Fin n, ((s : ℝ) - ν i - (i : ℕ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (i : ℕ)) ^ 2 =
      (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n) - 2 * s * ν i + (s : ℝ) ^ 2 + s * (n - 1) - 2 * s * (i : ℕ) := by
    intro i; ring
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  linear_combination (s : ℝ) * hm

theorem sum_shift (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    ∑ k, ((l k : ℝ) + (k : ℕ)) = n * s - ∑ i, (ν i : ℝ) := by
  have hl : ∀ i, (l (w i) : ℝ) = s - ν i - (i : ℕ) := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (h i)
    push_cast at this
    linarith
  rw [Finset.sum_add_distrib, ← Equiv.sum_comp w (fun k => (l k : ℝ))]
  simp only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end PositivityTheory.Rg.Cz.CGlue
