import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep

set_option autoImplicit false
noncomputable section
open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix
namespace GlobalTheory.GoodMetric.PolyRep
variable {ι : Type} {m : ι → ℕ}

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in

theorem _root_.GlobalTheory.GoodMetric.PolyRep.lie_proj_model [Fintype ι] (τ : ι) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) : (_root_.GlobalTheory.GoodMetric.PolyRep.proj m τ).lie A = A τ := by
  classical
  ext i j
  simp [_root_.GlobalTheory.GoodMetric.PolyRep.lie, _root_.GlobalTheory.GoodMetric.PolyRep.proj, pderiv_X, Pi.single_apply]
  rfl

def detModel (m : ι → ℕ) (τ : ι) : PolyRep m where
  M := 1
  ent := Matrix.of fun _ _ => (Matrix.of fun i j => (X ⟨τ, (i, j)⟩ : MvPolynomial (EntIx m) ℤ)).det
  one R _ := by
    ext i j
    have : i = j := Subsingleton.elim _ _
    subst this
    simp only [evEnt, Matrix.map_apply, Matrix.of_apply, AlgHom.map_det]
    have : (aeval (R := ℤ) fun v : EntIx m => (1 : Mat m R) v.1 v.2.1 v.2.2).mapMatrix
      (Matrix.of fun i j => (X ⟨τ, (i, j)⟩ : MvPolynomial (EntIx m) ℤ)) = 1 := by
      ext a b; simp
    rw [this]; simp
  mul R _ A B := by
    have h : ∀ C : Mat m R, (aeval (R := ℤ) fun v : EntIx m => C v.1 v.2.1 v.2.2).mapMatrix
      (Matrix.of fun i j => (X ⟨τ, (i, j)⟩ : MvPolynomial (EntIx m) ℤ)) = C τ := by
      intro C; ext a b; simp
    ext i j
    simp only [evEnt, Matrix.map_apply, Matrix.of_apply, AlgHom.map_det, h, Matrix.mul_apply]
    simp
  transp R _ A := by
    have h : ∀ C : Mat m R, (aeval (R := ℤ) fun v : EntIx m => C v.1 v.2.1 v.2.2).mapMatrix
      (Matrix.of fun i j => (X ⟨τ, (i, j)⟩ : MvPolynomial (EntIx m) ℤ)) = C τ := by
      intro C; ext a b; simp
    ext i j
    simp only [evEnt, Matrix.map_apply, Matrix.of_apply, AlgHom.map_det, h, Matrix.transpose_apply]
    have := h (fun τ => (A τ)ᵀ)
    simp only [Matrix.transpose_apply] at this
    rw [this]; simp

theorem aeval_dual_model {σ : Type} [Fintype σ] {R : Type} [CommRing R] (x a : σ → R) (p : MvPolynomial σ ℤ) :
    aeval (fun v => (TrivSqZeroExt.inl (x v) + TrivSqZeroExt.inr (a v) : DualNumber R)) p
      = TrivSqZeroExt.inl (aeval x p) + TrivSqZeroExt.inr (∑ v, aeval x (pderiv v p) * a v) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => ext <;> simp
  | add p q hp hq => rw [map_add, hp, hq]; ext <;> simp [add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, hp]
    ext
    · simp
    · simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, Finset.mul_sum, apply_ite]
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in
private lemma aeval_dualNumber_inl_add_inr {σ : Type} [Fintype σ] {R : Type} [CommRing R]
    (x y : σ → R) (p : MvPolynomial σ ℤ) :
    aeval (fun v => (TrivSqZeroExt.inl (x v) + TrivSqZeroExt.inr (y v) : DualNumber R)) p
      = TrivSqZeroExt.inl (aeval x p) + TrivSqZeroExt.inr (∑ v, aeval x (pderiv v p) * y v) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => ext <;> simp
  | add p q hp hq =>
    rw [map_add, hp, hq]
    ext <;> simp [Finset.sum_add_distrib, add_mul]
  | mul_X p v hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
        Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
        Finset.sum_add_distrib]
      simp [Pi.single_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, add_comm]

set_option autoImplicit false in
open MvPolynomial in
open scoped Matrix in
variable {ι : Type} {m : ι → ℕ} in

theorem _root_.GlobalTheory.GoodMetric.PolyRep.ev_dual_model [Fintype ι] (ρ : _root_.GlobalTheory.GoodMetric.PolyRep m) {R : Type} [CommRing R] (A : _root_.GlobalTheory.FlagBundle.Mat m R) (i j : Fin ρ.M) :
    ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : _root_.GlobalTheory.FlagBundle.Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b)) i j
      = TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) i j) + TrivSqZeroExt.inr (ρ.lie A i j) := by
  have h1 := congrFun (congrFun (ρ.one R) i) j
  simp only [_root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply] at h1
  simp only [_root_.GlobalTheory.GoodMetric.PolyRep.ev, _root_.GlobalTheory.GoodMetric.evEnt, Matrix.map_apply, Matrix.of_apply,
    _root_.GlobalTheory.GoodMetric.PolyRep.lie]
  refine (aeval_dualNumber_inl_add_inr (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => (1 : _root_.GlobalTheory.FlagBundle.Mat m R) v.1 v.2.1 v.2.2)
    (fun v : _root_.GlobalTheory.GoodMetric.EntIx m => A v.1 v.2.1 v.2.2) _).trans ?_
  rw [h1]

theorem ev_detModel (τ : ι) {R : Type} [CommRing R] (A : Mat m R) (i j : Fin 1) :
    (detModel m τ).ev A i j = (A τ).det := by
  have h : (aeval (R := ℤ) fun v : EntIx m => A v.1 v.2.1 v.2.2).mapMatrix
      (Matrix.of fun i j => (X ⟨τ, (i, j)⟩ : MvPolynomial (EntIx m) ℤ)) = A τ := by
    ext a b; simp
  rw [← h, ← AlgHom.map_det]; rfl

theorem lie_detModel [Fintype ι] (τ : ι) {R : Type} [CommRing R] (A : Mat m R) (i : Fin 1) :
    (detModel m τ).lie A i i = (A τ).trace := by
  have h := ev_dual_model (detModel m τ) A i i
  rw [ev_detModel] at h
  have h2 : (Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b) : DualNumber R))
      = 1 + (DualNumber.eps : DualNumber R) • (A τ).map TrivSqZeroExt.inl := by
    ext a b <;> by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [h2, Matrix.det_one_add_smul] at h
  have h3 := congrArg TrivSqZeroExt.snd h
  simp [pow_two, Matrix.trace, TrivSqZeroExt.fst_sum] at h3
  simp [Matrix.trace, h3]

theorem lie_transp_model [Fintype ι] (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) :
    ρ.lie (fun τ => (A τ)ᵀ) = (ρ.lie A)ᵀ := by
  ext i j
  have h1 := ev_dual_model ρ (fun τ => (A τ)ᵀ) i j
  have h2 := ev_dual_model ρ A j i
  have h3 := congrFun (congrFun (ρ.transp (DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b))) i) j
  have h4 : (fun τ => (Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b) : DualNumber R))ᵀ)
     = fun τ => Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr ((A τ)ᵀ a b) : DualNumber R) := by
    funext τ; ext a b <;> simp [Matrix.one_apply, eq_comm]
  rw [h4] at h3
  have h5 := h1.symm.trans (h3.trans h2)
  simpa using congrArg TrivSqZeroExt.snd h5

end GlobalTheory.GoodMetric.PolyRep
end
