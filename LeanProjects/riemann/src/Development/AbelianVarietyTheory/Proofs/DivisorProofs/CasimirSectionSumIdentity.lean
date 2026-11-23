import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryTAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointBlockOrthogonalityStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

noncomputable section

namespace GlobalTheory.SteepMult.CasDom

variable {R S : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem position_section (k : ℕ) (i : Fin k) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (Z : Mat R S) (L : Module.End ℂ W)
    (Ψ : (Fin k → NC R S) → W) :
    ∑ g, formT 1 B (factorOp 1 0 Z (section1 Ψ i g)) (fun h => L (section1 Ψ i g h)) =
      (Fintype.card (NC R S) : ℂ) * formT k B (factorOp k i Z Ψ) (fun g => L (Ψ g)) := by
  classical
  set s : (Fin k → NC R S) → ℂ := fun g' => B (factorOp k i Z Ψ g') (L (Ψ g')) with hs
  have h1 : ∀ g (h : Fin 1 → NC R S), B (factorOp 1 0 Z (section1 Ψ i g) h) (L (section1 Ψ i g h)) =
      s (Function.update g i (h 0)) := by
    intro g h
    simp [hs, factorOp, section1]
  have h2 : ∀ g, ∑ h : Fin 1 → NC R S, s (Function.update g i (h 0)) = ∑ y, s (Function.update g i y) := by
    intro g
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ (fun h => rfl)
  simp only [formT_apply, h1, h2]
  have := sum_update_swap i (fun (_ g' : Fin k → NC R S) => s g')
  rw [this]
  simp [Finset.sum_const, Finset.mul_sum, hs]

theorem adCoeff_casimir (z w : NC R S) :
    ∑ a, ∑ b, (if sameBlock a b then
      ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) =
      if z = w then ((R + S : ℕ) : ℂ) else 0 := by
  exact GlobalTheory.T.adjoint_block_orthogonality R S z w

lemma sum4' {α β γ δ M : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    ∑ i, ∑ g, ∑ a, ∑ b, f i g a b = ∑ a, ∑ b, ∑ i, ∑ g, f i g a b := by
  calc _ = ∑ i, ∑ a, ∑ b, ∑ g, f i g a b := Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem position_cas_of (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x : (Fin 1 → NC R S) → W)
    (hC : ∀ z w : NC R S, ∑ a, ∑ b, (if sameBlock a b then
      ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) =
      if z = w then ((R + S : ℕ) : ℂ) else 0) :
    ∑ a, ∑ b, (if sameBlock a b then formT 1 B (factorOp 1 0 (Eab b a) x) (factorOp 1 0 (Eab b a) x) else 0) =
      ((R + S : ℕ) : ℂ) * formT 1 B x x := by
  classical
  set X : NC R S → W := fun z => x (fun _ => z) with hX
  have hu : ∀ (h : Fin 1 → NC R S) z, Function.update h (0 : Fin 1) z = fun _ => z := by
    intro h z; funext j; rw [Subsingleton.elim j 0]; simp
  have hx : ∀ h : Fin 1 → NC R S, x h = X (h 0) := by
    intro h; simp only [hX]; congr 1; funext j; rw [Subsingleton.elim j 0]
  have hsum : ∀ F : NC R S → ℂ, ∑ h : Fin 1 → NC R S, F (h 0) = ∑ y, F y := fun F =>
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ (fun h => rfl)
  have hform : ∀ Z : Mat R S, formT 1 B (factorOp 1 0 Z x) (factorOp 1 0 Z x) =
      ∑ z, ∑ w, (∑ y, (starRingEnd ℂ) (adP Z y z) * adP Z y w) * B (X z) (X w) := by
    intro Z
    have e : ∀ h : Fin 1 → NC R S, factorOp 1 0 Z x h = ∑ z, adP Z (h 0) z • X z := by
      intro h; simp [factorOp, hu, hX]
    simp only [formT_apply, e]
    rw [hsum (fun y => B (∑ z, adP Z y z • X z) (∑ w, adP Z y w • X w))]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [RingHom.id_apply]
    ring
  have hr : formT 1 B x x = ∑ y, B (X y) (X y) := by
    simp only [formT_apply, hx]
    exact hsum (fun y => B (X y) (X y))
  calc _ = ∑ a, ∑ b, ∑ z, ∑ w, (if sameBlock a b then
        ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) * B (X z) (X w) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : sameBlock a b
        · simp only [if_pos h, hform]
        · simp [h]
    _ = ∑ z, ∑ w, ∑ a, ∑ b, (if sameBlock a b then
        ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) * B (X z) (X w) := sum4' _
    _ = ∑ z, ∑ w, (if z = w then ((R + S : ℕ) : ℂ) else 0) * B (X z) (X w) := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
        rw [← hC z w, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
    _ = _ := by
        rw [hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp [ite_mul]

theorem position_cas (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x : (Fin 1 → NC R S) → W) :
    ∑ a, ∑ b, (if sameBlock a b then formT 1 B (factorOp 1 0 (Eab b a) x) (factorOp 1 0 (Eab b a) x) else 0) =
      ((R + S : ℕ) : ℂ) * formT 1 B x x :=
  position_cas_of B x adCoeff_casimir

lemma same_symm' {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [sameBlock]

lemma tAct_split (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) :
    tAct k actW Z Ψ = (fun g => actW Z (Ψ g)) + (∑ i, factorOp k i Z) Ψ := by
  ext g
  simp [tAct_apply, factorOp, LinearMap.sum_apply, Finset.sum_apply]

lemma formT_herm (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ Φ : (Fin k → NC R S) → W) : (formT k B Φ Ψ).re = (formT k B Ψ Φ).re := by
  rw [formT_apply, formT_apply, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← hU.1 (Ψ g) (Φ g)]
  simp

lemma formT_nonneg (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) : 0 ≤ (formT k B Ψ Ψ).re := by
  rw [formT_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun g _ => ?_
  by_cases h : Ψ g = 0
  · simp [h]
  · exact (hU.2.1 _ h).le

lemma tAct_adj (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) {a b : Ix R S} (hab : sameBlock a b) (Ψ Φ : (Fin k → NC R S) → W) :
    formT k B (tAct k actW (Eab a b) Ψ) Φ = formT k B Ψ (tAct k actW (Eab b a) Φ) :=
  (isUnitary_tAct R S k W actW B hU).2.2 a b hab Ψ Φ

lemma casK_form (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ) = ∑ a, ∑ b, (if sameBlock a b then
      formT k B (tAct k actW (Eab b a) Ψ) (tAct k actW (Eab b a) Ψ) else 0) := by
  simp only [GlobalTheory.BlockReps.casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp only [GlobalTheory.BlockReps.unitK, if_pos h, if_pos (same_symm' h)]
    exact (tAct_adj k hU (same_symm' h) _ _).symm
  · simp [GlobalTheory.BlockReps.unitK, h]

lemma casK_pt (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g)) = ∑ a, ∑ b, (if sameBlock a b then
      formT k B (fun g => actW (Eab b a) (Ψ g)) (fun g => actW (Eab b a) (Ψ g)) else 0) := by
  simp only [formT_apply, GlobalTheory.BlockReps.casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp only [GlobalTheory.BlockReps.unitK, if_pos h, if_pos (same_symm' h)]
    exact Finset.sum_congr rfl fun g _ => (hU.2.2 b a (same_symm' h) _ _).symm
  · simp [GlobalTheory.BlockReps.unitK, h]

lemma diff_eq (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    (formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ)).re - (formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g))).re =
      ∑ a, ∑ b, (if sameBlock a b then
        (formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) ((∑ i, factorOp k i (Eab b a)) Ψ)).re +
        2 * (formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g))).re else 0) := by
  rw [casK_form k hU, casK_pt k hU, Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp only [if_pos h, tAct_split, map_add, LinearMap.add_apply, Complex.add_re]
    rw [formT_herm k hU ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g))]
    ring
  · simp [h]

lemma bracket_eq {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (x : (Fin 1 → NC R S) → W) :
    (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 actW) x)).re - ((R + S : ℕ) : ℝ) * (formT 1 B x x).re -
        (formT 1 B x (fun h => GlobalTheory.BlockReps.casK actW (x h))).re =
      ∑ a, ∑ b, (if sameBlock a b then
        2 * (formT 1 B (factorOp 1 0 (Eab b a) x) (fun h => actW (Eab b a) (x h))).re else 0) := by
  have h2 : ∑ a, ∑ b, (if sameBlock a b then
      (formT 1 B (factorOp 1 0 (Eab b a) x) (factorOp 1 0 (Eab b a) x)).re else 0) =
      ((R + S : ℕ) : ℝ) * (formT 1 B x x).re := by
    have := congrArg Complex.re (position_cas B x)
    simpa [Complex.re_sum, apply_ite Complex.re] using this
  have h1 := diff_eq 1 hU x
  simp only [Fin.sum_univ_one] at h1
  rw [sub_right_comm, h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

theorem casDom (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    ∑ i, ∑ g, ((formT 1 B (section1 Ψ i g) (GlobalTheory.BlockReps.casK (tAct 1 actW) (section1 Ψ i g))).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B (section1 Ψ i g) (section1 Ψ i g)).re -
        (formT 1 B (section1 Ψ i g) (fun h => GlobalTheory.BlockReps.casK actW (section1 Ψ i g h))).re) ≤
      (Fintype.card (NC R S) : ℝ) * ((formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ)).re -
        (formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g))).re) := by
  have hL : ∑ i, ∑ g, ((formT 1 B (section1 Ψ i g) (GlobalTheory.BlockReps.casK (tAct 1 actW) (section1 Ψ i g))).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B (section1 Ψ i g) (section1 Ψ i g)).re -
        (formT 1 B (section1 Ψ i g) (fun h => GlobalTheory.BlockReps.casK actW (section1 Ψ i g h))).re) =
      (Fintype.card (NC R S) : ℝ) * ∑ a, ∑ b, (if sameBlock a b then
        2 * (formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g))).re else 0) := by
    simp only [bracket_eq hU]
    rw [sum4', Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : sameBlock a b
    · simp only [if_pos h]
      have e : ∑ i, ∑ g, formT 1 B (factorOp 1 0 (Eab b a) (section1 Ψ i g))
            (fun h => actW (Eab b a) (section1 Ψ i g h)) =
          ((Fintype.card (NC R S) : ℝ) : ℂ) *
            formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g)) := by
        simp only [position_section, ← Finset.mul_sum, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
        push_cast
        rfl
      have e2 := congrArg Complex.re e
      rw [Complex.re_ofReal_mul, Complex.re_sum] at e2
      simp only [Complex.re_sum] at e2
      simp only [← Finset.mul_sum, e2]
      ring
    · simp [h]
  rw [hL, diff_eq k hU Ψ]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (Nat.cast_nonneg _)
  split_ifs
  · linarith [formT_nonneg k hU ((∑ i, factorOp k i (Eab b a)) Ψ)]
  · exact le_rfl

end GlobalTheory.SteepMult.CasDom

end
