import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatChain

section MulAlg

variable {K : Type} [Field K] {N : ℕ}

theorem diag_mul_of_blockTriangular {A B : Matrix (Fin N) (Fin N) K} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem smul_mem_matrix {R : Subring K} {c : K} {M : Matrix (Fin N) (Fin N) K} (hc : c ∈ R) (hM : M ∈ R.matrix) :
    c • M ∈ R.matrix := fun i j => R.mul_mem hc (hM i j)

end MulAlg

theorem triMod_mul_triMod : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (h b : K) (A A' : Matrix (Fin N) (Fin N) K) (d d' : Fin N → K), h ∈ R → b ∈ R → (b • A ∈ R.matrix → b • A' ∈ R.matrix → TriMod R (h * b) A d → TriMod R (h * b) A' d' → TriMod R h (A * A') fun i => d i * d' i) ∧ ∀ B B' : Matrix (Fin N) (Fin N) K, B.BlockTriangular id → B'.BlockTriangular id → B ∈ R.matrix → b • B' ∈ R.matrix → TriMod R (h * b) A d → TriMod R h (B * A * B') fun i => B i i * d i * B' i i := by
  intro K _ N R h b A A' d d' hh hb
  refine ⟨fun hbA hbA' ⟨E, hE, h1, h2⟩ ⟨E', hE', h1', h2'⟩ => ?_,
    fun B B' hB hB' hBR hbB' ⟨E, hE, h1, h2⟩ => ?_⟩
  · have key : A * A' - h • (E * (b • A') + (b • A) * E' - (h * b * b) • (E * E')) =
        (A - (h * b) • E) * (A' - (h * b) • E') := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, smul_smul]
      module
    refine ⟨_, sub_mem (add_mem (mul_mem hE hbA') (mul_mem hbA hE'))
      (smul_mem_matrix (R.mul_mem (R.mul_mem hh hb) hb) (mul_mem hE hE')), ?_, fun i => ?_⟩
    · rw [key]; exact h1.mul h1'
    · rw [key, diag_mul_of_blockTriangular h1 h1', h2, h2']
  · have key : B * A * B' - h • (B * E * (b • B')) = B * (A - (h * b) • E) * B' := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    refine ⟨_, mul_mem (mul_mem hBR hE) hbB', ?_, fun i => ?_⟩
    · rw [key]; exact (hB.mul h1).mul hB'
    · rw [key, diag_mul_of_blockTriangular (hB.mul h1) hB', diag_mul_of_blockTriangular hB h1, h2]

end GlobalTheory.LatChain

end
