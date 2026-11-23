import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.RealId

theorem lower_rows {n : ℕ} (p q r s : Matrix (Fin n) (Fin n) ℂ)
    (h : blk4 p q r s * (blk4 p q r s)ᴴ = 1) : r * rᴴ + s * sᴴ = 1 := by
  have h1 : Matrix.fromBlocks p q r s * (Matrix.fromBlocks p q r s)ᴴ = 1 := by
    have h2 := congrArg (fun M => Matrix.submatrix M (finSumFinEquiv (m := n) (n := n)) (finSumFinEquiv (m := n) (n := n))) h
    simpa [blk4, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_one_equiv] using h2
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h1
  exact (Matrix.fromBlocks_inj.1 h1).2.2.2

theorem block_matrix_map {R S : Type} {n : ℕ} (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  simp only [blk4]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem map_adj (D : D7) (φ : AE D →+* ℂ) (hφ : ∀ z, φ (cA D z) = conj (φ z)) {m n : ℕ} (x : Mx D m n) :
    (adj x).map φ = (x.map φ)ᴴ := by
  ext i j
  simp [adj, Matrix.conjTranspose_apply, hφ]

theorem det_id {n : ℕ} (A B C Dm : Matrix (Fin n) (Fin n) ℂ) (hu : A * Aᴴ + B * Bᴴ = 1)
    (hA : Dm * A = -1) (hB : Dm * B = -C) (hC : Cᴴ = C) :
    (1 + C * C).det.re = ‖Dm.det‖ ^ 2 := by
  have e : Dm * Dmᴴ = 1 + C * C := by
    calc Dm * Dmᴴ = Dm * (A * Aᴴ + B * Bᴴ) * Dmᴴ := by rw [hu, mul_one]
      _ = (Dm * A) * (Dm * A)ᴴ + (Dm * B) * (Dm * B)ᴴ := by
        simp only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]
      _ = 1 + C * C := by
        rw [hA, hB, Matrix.conjTranspose_neg, Matrix.conjTranspose_neg, hC]
        simp
  rw [← e, Matrix.det_mul, Matrix.det_conjTranspose]
  show (Dm.det * conj Dm.det).re = _
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem det_real_part_unitary_block_identity (D : D7) (n : ℕ) (φ : AE D →+* ℂ) (hconj : ∀ z, φ (cA D z) = conj (φ z))
    (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n)
    (hl : k₃.map φ * (k₃.map φ)ᴴ + k₄.map φ * (k₄.map φ)ᴴ = 1)
    (h3 : d.1 * k₃ = -1) (h4 : d.1 * k₄ = -(pull a b).1) :
    (1 + (((a⁻¹).1.map φ) * b.1.map φ * ((a⁻¹).1.map φ)ᴴ) * (((a⁻¹).1.map φ) * b.1.map φ * ((a⁻¹).1.map φ)ᴴ)).det.re
      = ‖φ (Matrix.GeneralLinearGroup.det d).1‖ ^ 2 := by
  have hmul : ∀ x y : Mx D n n, (x * y).map φ = x.map φ * y.map φ := fun x y => map_mul φ.mapMatrix x y
  have hneg : ∀ x : Mx D n n, (-x).map φ = -(x.map φ) := fun x => map_neg φ.mapMatrix x
  have hone : (1 : Mx D n n).map φ = 1 := map_one φ.mapMatrix
  have hC : ((pull a b).1).map φ = ((a⁻¹).1.map φ) * b.1.map φ * ((a⁻¹).1.map φ)ᴴ := by
    show ((a⁻¹).1 * b.1 * adj (a⁻¹).1).map φ = _
    rw [hmul, hmul, map_adj D φ hconj]
  have hherm : (((pull a b).1).map φ)ᴴ = ((pull a b).1).map φ := by
    rw [← map_adj D φ hconj]
    exact congrArg (fun M => Matrix.map M φ) (pull a b).2
  have hA : (d.1.map φ) * (k₃.map φ) = -1 := by
    rw [← hmul, h3, hneg, hone]
  have hB : (d.1.map φ) * (k₄.map φ) = -((pull a b).1.map φ) := by
    rw [← hmul, h4, hneg]
  rw [← hC, det_id _ _ _ _ hl hA hB hherm]
  have : (d.1.map φ).det = φ (Matrix.GeneralLinearGroup.det d).1 := (RingHom.map_det φ d.1).symm
  rw [this]

theorem det_one_add_sq : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₁ k₂ k₃ k₄ : Mx D n n) (τ : D.what₂.Tau), (blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)) * ((blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)))ᴴ = 1 → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → (1 + (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ) * (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ)).det.re = ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖ ^ 2 := by
  intro D n θ hθ a d b k₁ k₂ k₃ k₄ τ hu h3 h4
  have hconj : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = conj (((θ τ).comp (infPart D)) z) :=
    fun z => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 z τ
  have hg : ((gAt θ a τ)⁻¹).1 = (a⁻¹).1.map ((θ τ).comp (infPart D)) := by
    have : (gAt θ a τ)⁻¹ = Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D)) a⁻¹ :=
      (map_inv (Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D))) a).symm
    rw [this]; rfl
  have hb : (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) = b.1.map ((θ τ).comp (infPart D)) := by
    ext i j; rfl
  rw [block_matrix_map] at hu
  have hl := lower_rows _ _ _ _ hu
  rw [hg, hb]
  exact det_real_part_unitary_block_identity D n _ hconj a d b k₃ k₄ hl h3 h4

end GlobalTheory.CompanionTheory.MM.RealId
