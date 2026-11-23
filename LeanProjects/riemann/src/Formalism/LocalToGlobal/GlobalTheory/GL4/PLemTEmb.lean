import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTAmgm

noncomputable section

open NumberField Matrix
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def trR (a : E) : ℝ := (∑ σ : E →+* ℂ, σ a).re

theorem trR_eq (a : E) : trR a = ((Algebra.trace ℚ E a : ℚ) : ℝ) := by
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := a)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ a = ∑ φ : E →+* ℂ, φ a :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ ↦ rfl
  unfold trR
  rw [← h3, ← h2]
  simp

theorem trR_add (a b : E) : trR (a + b) = trR a + trR b := by
  simp [trR, Finset.sum_add_distrib]

theorem trR_star (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (a : E) : trR (star a) = trR a := by
  unfold trR
  simp only [hσ, ← star_sum]
  simp

structure Model (S : HSpace E) where
  Y : (E →+* ℂ) → Matrix (Fin S.rank) (Fin S.rank) ℂ
  hY : ∀ σ (y : S.V), ∑ i, ‖(Y σ *ᵥ fun j ↦ σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re

theorem model_exists (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) : Nonempty (Model S) := by
  have h : ∀ σ : E →+* ℂ, ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ,
      ∀ y : S.V, ∑ i, ‖(Y *ᵥ fun j ↦ σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re := by
    intro σ
    have hs := hsig σ
    rw [hpos σ] at hs
    obtain ⟨Y, -, hY⟩ := S.frame_of_pos σ (fun a ↦ hσ σ a) hs
    exact ⟨Y, hY⟩
  choose Y hY using h
  exact ⟨⟨Y, hY⟩⟩

abbrev Idx (S : HSpace E) := (E →+* ℂ) × Fin S.rank × Bool

def vec {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (x : S.V) : Fin S.rank → ℂ :=
  M.Y σ *ᵥ fun j ↦ σ (S.frame.repr x j)

theorem vec_add {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (x y : S.V) :
    vec M σ (x + y) = vec M σ x + vec M σ y := by
  unfold vec
  rw [← Matrix.mulVec_add]
  congr 1
  ext j
  simp

theorem vec_rat {S : HSpace E} (M : Model S) (σ : E →+* ℂ) (r : ℚ) (x : S.V) :
    vec M σ ((r : E) • x) = (r : ℂ) • vec M σ x := by
  unfold vec
  rw [← Matrix.mulVec_smul]
  congr 1
  ext j
  simp

def psi {S : HSpace E} (M : Model S) : S.V →+ EuclideanSpace ℝ (Idx S) where
  toFun x := WithLp.toLp 2 fun p ↦ if p.2.2 then (vec M p.1 x p.2.1).re else (vec M p.1 x p.2.1).im
  map_zero' := by
    ext p
    simp only [vec, map_zero, LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have h0 : (fun _ : Fin S.rank ↦ (0 : ℂ)) = 0 := rfl
    rw [h0, Matrix.mulVec_zero]
    split_ifs <;> simp
  map_add' x y := by
    ext p
    simp only [vec_add, Pi.add_apply, Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> rfl

theorem psi_apply {S : HSpace E} (M : Model S) (x : S.V) (p : Idx S) :
    psi M x p = if p.2.2 then (vec M p.1 x p.2.1).re else (vec M p.1 x p.2.1).im := rfl

theorem psi_rat {S : HSpace E} (M : Model S) (r : ℚ) (x : S.V) : psi M ((r : E) • x) = (r : ℝ) • psi M x := by
  ext p
  rw [PiLp.smul_apply, psi_apply, psi_apply, vec_rat]
  have : ((r : ℂ)) = ((r : ℝ) : ℂ) := by simp
  rw [this]
  split_ifs <;> simp [smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem norm_psi_sq {S : HSpace E} (M : Model S) (x : S.V) : ‖psi M x‖ ^ 2 = trR (S.hT x x) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, trR, Complex.re_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Fintype.sum_prod_type, ← M.hY σ x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_bool, psi_apply, psi_apply]
  simp only [if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [vec]
  ring

theorem inner_psi {S : HSpace E} (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (M : Model S) (x y : S.V) :
    ⟪psi M x, psi M y⟫_ℝ = trR (S.hT x y) := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add]
  have h1 := norm_psi_sq M (x + y)
  have h2 := norm_psi_sq M x
  have h3 := norm_psi_sq M y
  rw [sq] at h1 h2 h3
  rw [h1, h2, h3]
  have hsym : S.hT y x = star (S.hT x y) := (S.herm.eq x y).symm
  simp only [map_add, LinearMap.add_apply, trR_add, hsym, trR_star hσ]
  ring

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
