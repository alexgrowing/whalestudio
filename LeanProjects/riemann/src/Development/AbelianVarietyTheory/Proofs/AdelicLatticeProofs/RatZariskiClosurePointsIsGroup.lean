import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AevalSumElimEqZeroOfMemPtsStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in

theorem ptsGroup_map_ev {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι A) :
    φ (ev f g) = ev f (g.map φ) := by
  unfold ev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem ptsGroup_generic_map {R : Type} [CommRing R] [Algebra ℚ R] (g : Matrix ι ι R) :
    (Matrix.mvPolynomialX ι ι ℚ).map (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) = g := by
  ext i j
  simp [Matrix.mvPolynomialX]

theorem ptsGroup_ev_adjugate {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι R) : ev (ev f (Matrix.mvPolynomialX ι ι ℚ).adjugate) g = ev f g.adjugate := by
  have h := ptsGroup_map_ev (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) f
    (Matrix.mvPolynomialX ι ι ℚ).adjugate
  have h2 := AlgHom.map_adjugate (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2))
    (Matrix.mvPolynomialX ι ι ℚ)
  simp only [AlgHom.mapMatrix_apply] at h2
  rw [h2, ptsGroup_generic_map] at h
  exact h

theorem ptsGroup_ev_det {R : Type} [CommRing R] [Algebra ℚ R]
    (g : Matrix ι ι R) : ev ((Matrix.mvPolynomialX ι ι ℚ).det - 1) g = g.det - 1 := by
  have h2 := AlgHom.map_det (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2))
    (Matrix.mvPolynomialX ι ι ℚ)
  simp only [AlgHom.mapMatrix_apply] at h2
  rw [ptsGroup_generic_map] at h2
  unfold ev
  rw [map_sub, map_one, h2]

theorem ptsGroup_ev_one (R : Type) [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ) :
    ev f (1 : Matrix ι ι R) = algebraMap ℚ R (ev f (1 : Matrix ι ι ℚ)) := by
  have h := ptsGroup_map_ev (Algebra.ofId ℚ R) f (1 : Matrix ι ι ℚ)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h.symm

theorem ptsGroup_ev_mul {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ)
    (x y : Matrix ι ι R) :
    MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2))
      (ev f ((Matrix.of fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ)) *
        (Matrix.of fun i j => (MvPolynomial.X (Sum.inr (i, j)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ)))) =
      ev f (x * y) := by
  rw [ptsGroup_map_ev]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem pts_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∀ (R : Type) [CommRing R] [Algebra ℚ R], (1 : Matrix ι ι R) ∈ pts Γ R ∧ (∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, x * y ∈ pts Γ R) ∧ (∀ x ∈ pts Γ R, x.adjugate ∈ pts Γ R) ∧ ∀ x ∈ pts Γ R, x.det = 1 := by
  intro ι _ _ Γ hΓ R _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    have h1 := hf 1 hΓ.one_mem
    rw [ptsGroup_ev_one] at h1 ⊢
    rw [(map_eq_zero_iff _ (algebraMap ℚ ℂ).injective).1 h1, map_zero]
  · intro x hx y hy f hf
    rw [← ptsGroup_ev_mul]
    refine GlobalTheory.T.aeval_sum_elim_eq_zero_of_mem_pts' ι Γ hΓ.aut_mem _ ?_ R x hx y hy
    intro g hg h hh
    rw [ptsGroup_ev_mul]
    exact hf _ (hΓ.mul_mem g hg h hh)
  · intro x hx f hf
    rw [← ptsGroup_ev_adjugate]
    refine hx _ ?_
    intro g hg
    rw [ptsGroup_ev_adjugate]
    exact hf _ (hΓ.adj_mem g hg)
  · intro x hx
    rw [← sub_eq_zero, ← ptsGroup_ev_det]
    refine hx _ ?_
    intro g hg
    rw [ptsGroup_ev_det, hΓ.det_eq g hg, sub_self]

end GlobalTheory.ClassFin
