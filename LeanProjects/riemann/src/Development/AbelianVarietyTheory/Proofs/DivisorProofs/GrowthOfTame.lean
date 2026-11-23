import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def growth : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (g * infGL E a y)‖ ≤ C * height y ^ N}
  zero_mem' g := ⟨0, 0, fun y => by simp⟩
  add_mem' {f f'} h h' g := by
    obtain ⟨C, N, hC⟩ := h g
    obtain ⟨C', N', hC'⟩ := h' g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have h1 := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have q1 : 0 ≤ height y ^ N := le_trans zero_le_one (one_le_pow₀ h1)
    have q2 : 0 ≤ height y ^ N' := le_trans zero_le_one (one_le_pow₀ h1)
    calc ‖(f + f') (g * infGL E a y)‖ ≤ ‖f (g * infGL E a y)‖ + ‖f' (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (hC y) (hC' y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) q1).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') q2).trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring
  smul_mem' c f h g := by
    obtain ⟨C, N, hC⟩ := h g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)

variable (E a) in

def tame : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ l : List (Lie E a), ((l.map (lie E a)).prod ψ).1 ∈ growth E a}
  zero_mem' l := by simp
  add_mem' {ψ ψ'} h h' l := by
    rw [map_add, Submodule.coe_add]
    exact add_mem (h l) (h' l)
  smul_mem' c ψ h l := by
    rw [map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ c (h l)

theorem growth_of_tame {ψ : Sm E a} (h : ψ ∈ tame E a) : ψ.1 ∈ growth E a := by
  simpa using h []

theorem lie_mem_tame (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ tame E a) : lie E a X ψ ∈ tame E a := by
  intro l
  have e : (l.map (lie E a)).prod (lie E a X ψ) = ((l ++ [X]).map (lie E a)).prod ψ := by
    simp [List.map_append, List.prod_append, Module.End.mul_apply]
  rw [e]
  exact h _

def dens (X : Lie E a) (α : Lie E a → ℂ) (x : Lie E a) : ℂ :=
  -(fderiv ℝ α x (lmul X x) + (LinearMap.trace ℝ (Lie E a) (lmul X).toLinearMap : ℂ) * α x)

def KInv (α : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a),
    α (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = α x

def maps (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a))
    (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) : Submodule ℂ (W →ₗ[ℂ] Sm E a) where
  carrier := {T | (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
    ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w}
  zero_mem' := ⟨fun k w => by simp, fun w => ⟨by simp, fun _ _ => rfl, fun k _ => by simp⟩⟩
  add_mem' {T T'} h h' := ⟨fun k w => by simp [h.1 k w, h'.1 k w], fun w =>
    ⟨by simpa using add_mem (h.2 w).1 (h'.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g, (h'.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk, (h'.2 w).2.2 k hk]⟩⟩
  smul_mem' c T h := ⟨fun k w => by simp [h.1 k w], fun w =>
    ⟨by simpa using Submodule.smul_mem _ c (h.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk]⟩⟩

theorem isTest_dens (X : Lie E a) {α : Lie E a → ℂ} (h : GlobalTheory.CuspQuot.IsTest (invSet E a) α) :
    GlobalTheory.CuspQuot.IsTest (invSet E a) (dens X α) := by
  have hs : Function.support (dens X α) ⊆ tsupport α := by
    intro x hx
    by_contra hn
    apply hx
    have h1 : α x = 0 := image_eq_zero_of_notMem_tsupport hn
    have h2 : fderiv ℝ α x = 0 := fderiv_of_notMem_tsupport ℝ hn
    simp [dens, h1, h2]
  have ht : tsupport (dens X α) ⊆ tsupport α := closure_minimal hs (isClosed_tsupport α)
  refine ⟨?_, h.2.1.mono' hs, ht.trans h.2.2⟩
  refine (((h.1.fderiv_right (m := ∞) (by simp)).clm_apply (lmul X).contDiff).add
    (contDiff_const.mul h.1)).neg

end GlobalTheory.AutGrowth
