import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def sv (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1))) (x : Mt g (m + 1)) (v : τ) : τ :=
  ∑ y : Gn g (m + 1), (ψ₀ (trace (x * (y : Mt g (m + 1)))) : ℂ) • τ.ρ y⁻¹ v

def Hm (b : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if k = 0 then b i else (1 : Mt g (m + 1)) i k

def Ez : Mt g (m + 1) := Matrix.diagonal fun i : Fin (m + 1) => if i = 0 then (0 : ZMod g) else 1

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

theorem rho_inv_mul_apply (y a : Gn g (m + 1)) (v : τ) : τ.ρ (y⁻¹ * a⁻¹) (τ.ρ a v) = τ.ρ y⁻¹ v := by
  rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ.ρ a⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem rho_mul_inv_apply (y a : Gn g (m + 1)) (v : τ) : τ.ρ a (τ.ρ (a⁻¹ * y⁻¹) v) = τ.ρ y⁻¹ v := by
  rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ.ρ a), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

theorem sv_mul_right (x : Mt g (m + 1)) (a : Gn g (m + 1)) (v : τ) :
    sv ψ₀ τ (x * (a : Mt g (m + 1))) v = sv ψ₀ τ x (τ.ρ a v) := by
  unfold sv
  refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun y => ?_)
  rw [Equiv.coe_mulLeft]
  beta_reduce
  rw [Units.val_mul, ← Matrix.mul_assoc, _root_.mul_inv_rev, rho_inv_mul_apply]

theorem sv_mul_left (a : Gn g (m + 1)) (x : Mt g (m + 1)) (v : τ) :
    sv ψ₀ τ ((a : Mt g (m + 1)) * x) v = τ.ρ a (sv ψ₀ τ x v) := by
  unfold sv
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun y => ?_)
  have ht : trace ((a : Mt g (m + 1)) * x * (y : Mt g (m + 1))) =
      trace (x * ((y * a : Gn g (m + 1)) : Mt g (m + 1))) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm (x * (y : Mt g (m + 1))), ← Matrix.mul_assoc]
  rw [Equiv.coe_mulRight]
  beta_reduce
  rw [map_smul, _root_.mul_inv_rev, rho_mul_inv_apply, ht]

theorem sv_unit {γ : ℂ}
    (hγ : ∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v)
    (a : Gn g (m + 1)) (v : τ) : sv ψ₀ τ (a : Mt g (m + 1)) v = γ • τ.ρ a v := by
  have h1 : sv ψ₀ τ 1 v = γ • v := by
    unfold sv
    rw [← hγ v, finsum_eq_sum_of_fintype]
    simp only [Matrix.one_mul]
  have := sv_mul_left ψ₀ τ a 1 v
  rw [Matrix.mul_one, h1, map_smul] at this
  exact this

theorem sv_sum {ι : Type} (s : Finset ι) (x : Mt g (m + 1)) (f : ι → τ) :
    sv ψ₀ τ x (∑ i ∈ s, f i) = ∑ i ∈ s, sv ψ₀ τ x (f i) := by
  unfold sv
  simp_rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem sv_zero (x : Mt g (m + 1)) : sv ψ₀ τ x 0 = 0 := by
  simp [sv]

theorem Ez_mul_unip (u : Gn g (m + 1))
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1)) :
    (Ez : Mt g (m + 1)) * (u : Mt g (m + 1)) = Ez := by
  ext i k
  rw [Ez, Matrix.diagonal_mul]
  by_cases hi : i = 0
  · subst hi
    simp [Matrix.diagonal_apply]
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have hb : GlobalTheory.FiniteGL.twoBlocks (m + 1) 1 k ≤ GlobalTheory.FiniteGL.twoBlocks (m + 1) 1 i := by
      simp only [GlobalTheory.FiniteGL.twoBlocks]
      split_ifs <;> omega
    have h0 := (GlobalTheory.FiniteGL.mem_unipRadical.1 hu) i k hb
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [if_neg hi, one_mul, h0, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all

theorem sv_Ez (hτ : IsCusp τ.character) (hm : 0 < m) (v : τ) : sv ψ₀ τ Ez v = 0 := by
  have h1 : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
      sv ψ₀ τ Ez v = sv ψ₀ τ Ez (τ.ρ (u : Gn g (m + 1)) v) := fun u => by
    rw [← sv_mul_right, Ez_mul_unip _ u.2]
  have hsum := DiscreteGroups.sglob.DzLc.sum_unip_eq_zero τ hτ (a := 1) one_pos (by omega)
  have h2 : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1)) : ℂ) •
      sv ψ₀ τ Ez v = 0 := by
    calc _ = ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
          sv ψ₀ τ Ez (τ.ρ (u : Gn g (m + 1)) v) := by
          rw [← Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      _ = sv ψ₀ τ Ez ((∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
          τ.ρ (u : Gn g (m + 1))) v) := by rw [LinearMap.sum_apply, sv_sum]
      _ = 0 := by rw [hsum, LinearMap.zero_apply, sv_zero]
  exact (smul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem hm_mul (b c : Fin (m + 1) → ZMod g) :
    (Hm b : Mt g (m + 1)) * Hm c = Hm (fun i => b i * c 0 + if i = 0 then 0 else c i) := by
  ext i k
  rw [Matrix.mul_apply]
  by_cases hk : k = 0
  · subst hk
    rw [Fin.sum_univ_succ]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp [Hm, Matrix.one_apply, Fin.succ_ne_zero]
      exact Finset.sum_eq_zero (fun x _ => if_neg (Fin.succ_ne_zero x).symm)
    · simp [Hm, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj]
  · have hc : ∀ l, Hm c l k = (1 : Mt g (m + 1)) l k := fun l => by simp [Hm, hk]
    rw [Finset.sum_congr rfl (fun l _ => by rw [hc l]), ← Matrix.mul_apply, Matrix.mul_one]
    simp [Hm, hk]

theorem hm_zero : (Hm (0 : Fin (m + 1) → ZMod g) : Mt g (m + 1)) = Ez := by
  ext i k
  simp only [Hm, Ez, Matrix.of_apply, Pi.zero_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hk : k = 0
  · subst hk; split_ifs <;> simp_all
  · split_ifs <;> simp_all

theorem det_hm (b : Fin (m + 1) → ZMod g) : (Hm b : Mt g (m + 1)).det = b 0 := by
  have hl : (Hm b : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
    intro i k hik
    have hik' : i < k := hik
    have hk : k ≠ 0 := fun h => by subst h; exact absurd hik' (Fin.not_lt_zero i)
    simp [Hm, hk, Matrix.one_apply, ne_of_lt hik']
  rw [Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_succ]
  simp [Hm, Fin.succ_ne_zero]

def hmGL (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hm b) (by rw [det_hm]; exact hb)

theorem hmGL_val (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : ((hmGL b hb : Gn g (m + 1)) : Mt g (m + 1)) = Hm b :=
  rfl

theorem sv_singular (hτ : IsCusp τ.character) (hm : 0 < m) (u : Gn g (m + 1)) (b : Fin (m + 1) → ZMod g)
    (hb : b 0 = 0) (v : τ) : sv ψ₀ τ ((u : Mt g (m + 1)) * Hm b) v = 0 := by
  set c : Fin (m + 1) → ZMod g := fun i => (if i = 0 then 1 else 0) - b i with hc
  have hc0 : c 0 ≠ 0 := by simp [hc, hb]
  have hprod : (Hm b : Mt g (m + 1)) * ((hmGL c hc0 : Gn g (m + 1)) : Mt g (m + 1)) = Ez := by
    rw [hmGL_val, hm_mul, ← hm_zero]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi; simp [hc, hb]
    · simp [hc, hi, hb]
  have hH : (Hm b : Mt g (m + 1)) = Ez * (((hmGL c hc0)⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) := by
    rw [← hprod, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [sv_mul_left, hH, sv_mul_right, sv_Ez ψ₀ τ hτ hm, map_zero]

end DiscreteGroups.sglob.DzFe
