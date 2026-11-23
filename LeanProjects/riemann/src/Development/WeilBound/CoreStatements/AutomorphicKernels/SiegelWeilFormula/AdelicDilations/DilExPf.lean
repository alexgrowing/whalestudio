import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dilEx_pf (n : ℕ) (X : Fin n → ℝ) (τ : ℝ) : ∃ y : GR n, IsDil X τ y := by
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => (Real.exp (τ * X j) : ℂ) with hD
  set D' : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => (Real.exp (-(τ * X j)) : ℂ) with hD'
  have h1 : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]; congr 1; funext j; simp only [Pi.star_apply]; exact Complex.conj_ofReal _
  have h2 : D'ᴴ = D' := by
    rw [hD', Matrix.diagonal_conjTranspose]; congr 1; funext j; simp only [Pi.star_apply]; exact Complex.conj_ofReal _
  have h3 : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have h4 : D' * D = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hg : InG (Matrix.fromBlocks D 0 0 D') := by
    unfold InG JJ
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [h1, h2, h3, h4]
  exact ⟨Krd.DM.mkG _ hg, rfl⟩

theorem decW_pf {d : SD σ} (R : RD d) (w : InfinitePlace F) (x : d.G) :
    ∃ (x' : d.G) (y : GR d.n), x = x' * R.ι w y ∧ ∀ y' : GR d.n, x' * R.ι w y' = R.ι w y' * x' := by
  obtain ⟨x', y, h, hx⟩ := KSplitW.decompW d R w x
  exact ⟨x', y, h, KSplitW.commW d R w x' hx⟩

end PositivityTheory.SiegelWeilFormula.AStep

end
