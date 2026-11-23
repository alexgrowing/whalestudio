import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

theorem UpperTheory.grSq_transpose_inverse :
    ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ), M.PosDef → ∀ i : Fin m, GlobalTheory.GradedNorm.grSq Mᵀ i = GlobalTheory.GradedNorm.grSq M i ∧ GlobalTheory.GradedNorm.grSq ((M⁻¹).submatrix Fin.rev Fin.rev) i = (GlobalTheory.GradedNorm.grSq M i.rev)⁻¹ := by
  intro m M h i
  constructor
  · have e (k : Fin (m + 1)) : ReciprocityTheory.ChartRestriction.G.FD.lminor Mᵀ k = ReciprocityTheory.ChartRestriction.G.FD.lminor M k := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      rw [← Matrix.det_transpose]
      rfl
    rw [GlobalTheory.GradedNorm.grSq, GlobalTheory.GradedNorm.grSq, e, e]
  · obtain ⟨U, hU⟩ : ∃ U, U = (LDL.lowerInv h)ᴴ := ⟨_, rfl⟩
    have hT : ∀ a c, c < a → U a c = 0 := fun a c hc => by simp [hU, LDL.lowerInv_triangular h hc]
    have hu : IsUnit U.det := by
      rw [hU, det_conjTranspose]; exact (isUnit_det_of_invertible _).star
    have hd : ∀ a, U a a ≠ 0 := fun a => by
      rw [det_of_upperTriangular (M := U) fun _ _ h => hT _ _ h] at hu
      exact Finset.prod_ne_zero_iff.1 hu.ne_zero a (Finset.mem_univ _)
    have hD : Uᴴ * M * U = diagonal (LDL.diagEntries h) := by
      rw [hU, conjTranspose_conjTranspose]; exact (LDL.diag_eq_lowerInv_conj h).symm
    have hp : ∀ a, 0 < LDL.diagEntries h a := posDef_diagonal_iff.1
      (hD ▸ h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hu)))
    obtain ⟨d, hd0, hD⟩ : ∃ d : Fin m → ℝ, (∀ a, 0 < d a) ∧ Uᴴ * M * U = diagonal fun a => (d a : ℂ) :=
      ⟨fun a => (LDL.diagEntries h a).re, fun a => (Complex.pos_iff.1 (hp a)).1, hD.trans (congrArg _ (funext fun a =>
        Complex.ext rfl (Complex.pos_iff.1 (hp a)).2.symm))⟩
    have e1 : d i.rev = ‖U i.rev i.rev‖ ^ 2 * GlobalTheory.GradedNorm.grSq M i.rev := by
      rw [← GlobalTheory.GradedNorm.grSq_tri M hT hd, hD, GlobalTheory.GradedNorm.grSq_diagonal fun a => (hd0 a).ne']
    have e2 : M⁻¹ = U * (diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
      apply Matrix.inv_eq_right_inv
      have : Uᴴ * (M * U * (diagonal fun a => (((d a)⁻¹ : ℝ) : ℂ))) = 1 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext a
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hd0 a).ne', Complex.ofReal_one]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact mul_eq_one_comm.1 this
    have e3 : (M⁻¹).submatrix Fin.rev Fin.rev = ((Uᴴ).submatrix Fin.rev Fin.rev)ᴴ *
        (diagonal fun a : Fin m => (((d a.rev)⁻¹ : ℝ) : ℂ)) * (Uᴴ).submatrix Fin.rev Fin.rev := by
      rw [e2, Matrix.submatrix_mul _ _ _ Fin.rev _ Fin.rev_bijective,
        Matrix.submatrix_mul _ _ _ Fin.rev _ Fin.rev_bijective, conjTranspose_submatrix,
        conjTranspose_conjTranspose, submatrix_diagonal _ _ Fin.rev_injective]
      rfl
    have hn : ‖U i.rev i.rev‖ ≠ 0 := norm_ne_zero_iff.2 (hd _)
    have hg := (GlobalTheory.GradedNorm.grSq_pos h i.rev).ne'
    rw [e3, GlobalTheory.GradedNorm.grSq_tri _ (fun a c hc => by simp [hT _ _ (Fin.rev_lt_rev.2 hc)])
      (fun a => by simp [hd]), GlobalTheory.GradedNorm.grSq_diagonal (d := fun a => (d a.rev)⁻¹)
      (fun a => inv_ne_zero (hd0 _).ne'), e1, submatrix_apply, conjTranspose_apply, norm_star]
    field_simp
