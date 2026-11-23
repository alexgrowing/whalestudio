import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothHypersurfaceLocalCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

private theorem algebraMap_mem_nonZeroDivisors_of_flat {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have key : ∀ x : A, algebraMap R A r * x = 0 → x = 0 := by
    intro x hx
    have hsm : r • x = r • (0 : A) := by
      rw [smul_zero, Algebra.smul_def]
      exact hx
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr hsm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

private theorem coord_mem_nonZeroDivisors_of_isAffineOpen {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (j : Fin m) :
    c.coord j ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) := by
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) :=
    c.algebra_etale hU
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)) :=
    inferInstance
  have halg : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)))
      = c.coordRingHom := c.algebraMap_eq_coordRingHom
  have hXne : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hXnzd : (MvPolynomial.X (ULift.up.{u} j) : MvPolynomial (ULift.{u} (Fin m)) k)
      ∈ nonZeroDivisors (MvPolynomial (ULift.{u} (Fin m)) k) :=
    mem_nonZeroDivisors_of_ne_zero hXne
  have key : (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) ↑(X.presheaf.obj (op U)))
      (MvPolynomial.X (ULift.up.{u} j)) ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) :=
    algebraMap_mem_nonZeroDivisors_of_flat hXnzd
  rw [halg] at key
  rwa [c.coordRingHom_X j] at key

end

section

variable {R : Type*} [CommRing R]

theorem exists_unit_mul_of_span_eq {a b : R} (hb : b ∈ nonZeroDivisors R)
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    ∃ u : Rˣ, a = (u : R) * b := by
  have ha : a ∈ Ideal.span ({b} : Set R) := by
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  have hb' : b ∈ Ideal.span ({a} : Set R) := by
    rw [h]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hb'
  have hcancel : ∀ z : R, z * b = 0 → z = 0 := (mem_nonZeroDivisors_iff.mp hb).2
  have hzero : (d * c - 1) * b = 0 := by
    have hx : d * c * b = b := by rw [mul_assoc, hc, hd]
    rw [sub_mul, one_mul, hx, sub_self]
  have hdc : d * c = 1 := sub_eq_zero.mp (hcancel _ hzero)
  refine ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, hc.symm⟩

end

section

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

theorem derivation_mapsTo_span_self {B : Type*} [CommRing B] [Algebra k B]
    (D : Derivation k B B) (h : B) (hD : D h = 0) :
    ∀ x ∈ Ideal.span ({h} : Set B), D x ∈ Ideal.span ({h} : Set B) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Derivation.leibniz, hD, smul_zero, zero_add, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)

theorem algHom_map_derivation_eq_zero (π : R →ₐ[k] S) (h : R)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) :
    ∀ r : R, π r = 0 → π (D r) = 0 := by
  intro r hr
  have hrk : r ∈ Ideal.span ({h} : Set R) := by
    rw [← hker]
    exact hr
  have h2 : D r ∈ Ideal.span ({h} : Set R) := derivation_mapsTo_span_self D h hD r hrk
  rw [← hker] at h2
  have h3 : π.toRingHom (D r) = 0 := RingHom.mem_ker.mp h2
  exact h3

def liftDerivationOfKerEqSpan (π : R →ₐ[k] S) (hπ : Function.Surjective π) (h : R)
    (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) : Derivation k S S :=
  D.liftOfSurjective hπ (algHom_map_derivation_eq_zero π h hker D hD)

theorem liftDerivationOfKerEqSpan_apply (π : R →ₐ[k] S) (hπ : Function.Surjective π)
    (h : R) (hker : RingHom.ker π.toRingHom = Ideal.span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) (r : R) :
    liftDerivationOfKerEqSpan π hπ h hker D hD (π r) = π (D r) :=
  D.liftOfSurjective_apply hπ (algHom_map_derivation_eq_zero π h hker D hD) r

end

section

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

private theorem det_eq_det_submatrix_succ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ b : Fin (n + 1), M 0 b = if b = 0 then (1 : R) else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [h, Fin.succAbove_zero]
  · intro b _ hb
    simp [h b, hb]
  · intro hb
    exact absurd (Finset.mem_univ (0 : Fin (n + 1))) hb

theorem det_eq_det_submatrix_of_row_eq_single (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)
    (h : ∀ b : ι, M (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by
  have hN : ∀ b : Fin (n + 1),
      (M.submatrix e.symm e.symm) 0 b = if b = 0 then (1 : R) else 0 := by
    intro b
    simp only [Matrix.submatrix_apply]
    rw [h (e.symm b)]
    by_cases hb : b = 0
    · simp [hb]
    · have hne : ¬ (e.symm b = e.symm 0) := fun hc => hb (e.symm.injective hc)
      rw [if_neg hne, if_neg hb]
  have h2 := det_eq_det_submatrix_succ (M.submatrix e.symm e.symm) hN
  rw [Matrix.det_submatrix_equiv_self] at h2
  rw [h2, Matrix.submatrix_submatrix]
  rfl

theorem det_eq_det_submatrix_of_col_eq_single (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)
    (h : ∀ a : ι, M a (e.symm 0) = if a = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by
  have h' : ∀ b : ι, M.transpose (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0 :=
    fun b => h b
  have h1 := det_eq_det_submatrix_of_row_eq_single e M.transpose h'
  rw [Matrix.det_transpose] at h1
  rw [h1, ← Matrix.transpose_submatrix, Matrix.det_transpose]

end

section

variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem exists_unit_mul_coord_of_span_eq (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n) (g : Γ(X, U))
    (h : Ideal.span ({g} : Set Γ(X, U)) = Ideal.span ({c.coord j} : Set Γ(X, U))) :
    ∃ v : (Γ(X, U))ˣ, g = (v : Γ(X, U)) * c.coord j :=
  exists_unit_mul_of_span_eq (coord_mem_nonZeroDivisors_of_isAffineOpen hU c j) h

end

end FunctorialResolution.EmbeddedResolution
