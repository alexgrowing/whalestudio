import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.UnipCoords

variable (R : Type) [CommRing R] (n : ℕ)

def strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : i < j then x ⟨(i, j), h⟩ else 0

theorem det_one_add_strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (1 + strictUpper R n x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [strictUpper]
  · intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [strictUpper, h1, h2, Matrix.one_apply_ne h2]

def unitOf (x : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R where
  val := 1 + strictUpper R n x
  inv := (1 + strictUpper R n x).adjugate
  val_inv := by rw [Matrix.mul_adjugate, det_one_add_strictUpper, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, det_one_add_strictUpper, one_smul]

theorem unitOf_mem (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    unitOf R n x ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h1 : ¬ i < j := not_lt.2 (le_of_lt hji)
    have h2 : i ≠ j := ne_of_gt hji
    simp [unitOf, strictUpper, h1, Matrix.one_apply_ne h2]
  · simp [unitOf, strictUpper]

end GlobalTheory.UnipCoords

open GlobalTheory.UnipCoords in
theorem GlobalTheory.UnipCoords.unipCoordsHomeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  intro R _ _ _ n
  have hX : Continuous (fun x : {p : Fin n × Fin n // p.1 < p.2} → R => strictUpper R n x) := by
    refine continuous_matrix fun i j => ?_
    by_cases h : i < j
    · simp only [strictUpper, Matrix.of_apply, h, dite_true]; exact continuous_apply _
    · simp only [strictUpper, Matrix.of_apply, h, dite_false]; exact continuous_const
  let e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    { toFun := fun u p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
      invFun := fun x => ⟨unitOf R n x, unitOf_mem R n x⟩
      left_inv := by
        rintro ⟨u, hu⟩
        obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
        apply Subtype.ext; apply Units.ext; ext i j
        change (1 + strictUpper R n _) i j = _
        rcases lt_trichotomy i j with h | h | h
        · simp [strictUpper, h, Matrix.one_apply_ne (ne_of_lt h)]
        · subst h; simp [strictUpper, h2]
        · have h' : ¬ i < j := not_lt.2 (le_of_lt h)
          simp [strictUpper, h', Matrix.one_apply_ne (ne_of_gt h), h1 i j h]
      right_inv := by
        intro x; funext p
        change (1 + strictUpper R n x) p.1.1 p.1.2 = x p
        simp [strictUpper, p.2, Matrix.one_apply_ne (ne_of_lt p.2)] }
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun u => rfl⟩
  · refine continuous_pi fun p => ?_
    have hv : Continuous (fun u : GlobalTheory.SmGL.unipB R (Fin n) => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
    exact (continuous_apply_apply p.1.1 p.1.2).comp hv
  · refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_const.add hX
    · exact (continuous_const.add hX).matrix_adjugate
