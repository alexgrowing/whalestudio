import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

section Lin
variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k]

theorem gl_mulVec_inv_mulVec (X : GL n k) (v : n → k) :
    (X : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_inv_mulVec_mulVec (X : GL n k) (v : n → k) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ ((X : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_conj_mulVec (X g : GL n k) (v : n → k) :
    ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v =
      (X : Matrix n n k) *ᵥ ((g : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul]

theorem conj_fix_hyperplane_iff (X g : GL n k) (a : n → k) :
    (∀ v, a ⬝ᵥ v = 0 → ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v = v) ↔
      ∀ w, (a ᵥ* (X : Matrix n n k)) ⬝ᵥ w = 0 → (g : Matrix n n k) *ᵥ w = w := by
  constructor
  · intro h w hw
    have h1 := h ((X : Matrix n n k) *ᵥ w) (by rw [Matrix.dotProduct_mulVec]; exact hw)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    simpa only [gl_inv_mulVec_mulVec] using h2
  · intro h v hv
    rw [gl_conj_mulVec, h _ (by rw [← Matrix.dotProduct_mulVec, gl_mulVec_inv_mulVec]; exact hv),
      gl_mulVec_inv_mulVec]

theorem conj_triv_mod_line_iff (X g : GL n k) (a : n → k) :
    (∀ v, ∃ c : k, ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v - v = c • a) ↔
      ∀ w, ∃ c : k, (g : Matrix n n k) *ᵥ w - w = c • (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a) := by
  constructor
  · intro h w
    obtain ⟨c, h1⟩ := h ((X : Matrix n n k) *ᵥ w)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    exact ⟨c, by simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_inv_mulVec_mulVec] using h2⟩
  · intro h v
    obtain ⟨c, h1⟩ := h (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)
    have h2 := congrArg (fun u => (X : Matrix n n k) *ᵥ u) h1
    refine ⟨c, ?_⟩
    rw [gl_conj_mulVec]
    simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_mulVec_inv_mulVec] using h2

theorem vecMul_gl_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) : a ᵥ* (X : Matrix n n k) ≠ 0 := by
  intro h
  apply ha
  have h2 := congrArg (fun u => u ᵥ* ((X⁻¹ : GL n k) : Matrix n n k)) h
  simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  exact h2

theorem gl_inv_mulVec_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a ≠ 0 := by
  intro h
  apply ha
  rw [← gl_mulVec_inv_mulVec X a, h, Matrix.mulVec_zero]

theorem det_conj_gl (X g : GL n k) :
    Matrix.GeneralLinearGroup.det (X * g * X⁻¹) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem ite_congr_of_iff {p q : Prop} {dp : Decidable p} {dq : Decidable q} {u v : ℂ} (h : p ↔ q) :
    @ite ℂ p dp u v = @ite ℂ q dq u v := if_congr h rfl rfl

end Lin

theorem mirC_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ) (x : G), ∃ a' : Fin D.R.r → kP PP.1, a' ≠ 0 ∧ ∀ g, mirC R i PP a tr ε (x * g * x⁻¹) = mirC R i PP a' tr ε g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP a ha tr ε x
  have he : ∀ g PP', R.eG (x * g * x⁻¹) PP' = R.eG x PP' * R.eG g PP' * (R.eG x PP')⁻¹ := by
    intro g PP'
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : ∀ g, (∀ PP', PP' ≠ PP → R.eG (x * g * x⁻¹) PP' = 1) ↔ ∀ PP', PP' ≠ PP → R.eG g PP' = 1 := by
    intro g
    refine forall_congr' fun PP' => forall_congr' fun _ => ?_
    rw [he, conj_eq_one_iff]
  have h2 : ∀ g, Matrix.GeneralLinearGroup.det (R.eG (x * g * x⁻¹) PP) = Matrix.GeneralLinearGroup.det (R.eG g PP) := by
    intro g
    rw [he]
    exact det_conj_gl _ _
  cases tr
  · refine ⟨_, vecMul_gl_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_fix_hyperplane_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    exact h3
  · refine ⟨_, gl_inv_mulVec_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_triv_mod_line_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_pos rfl, if_pos rfl]
    exact h3

end GlobalTheory.DownLift.GenFinite
