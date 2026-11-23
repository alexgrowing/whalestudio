import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Unip

variable {D : D7} {n : ℕ}

theorem halfTr_add' (a c : AE D) : halfTr (a + c) = halfTr a + halfTr c := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_add, mul_add]

theorem halfTr_add_cA (s : AE D) : halfTr s + halfTr (cA D s) = trA s := by
  have hinv : Function.Involutive (cA D) := by
    intro a
    have h := congrArg (fun N => N 0 0)
      (GlobalTheory.MixModel.adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a))
    simpa [GlobalTheory.MixModel.adj] using h
  have hcomm : ∀ r : AF D.host.F, cA D (algebraMap (AF D.host.F) (AE D) r) =
      algebraMap (AF D.host.F) (AE D) r := by
    intro r
    simp [Formalism.L2.Theta.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  let e : AE D ≃ₐ[AF D.host.F] AE D :=
    AlgEquiv.ofBijective { cA D with commutes' := hcomm } hinv.bijective
  have htr : trA (cA D s) = trA s := Algebra.trace_eq_of_algEquiv e s
  simp only [GlobalTheory.StdUnn.halfTr]
  rw [htr, ← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem inner_add_add (V : HSp D) (z x : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (z + x) (z + x) = GlobalTheory.StdUnn.inner V z z + GlobalTheory.StdUnn.inner V z x + GlobalTheory.StdUnn.inner V x z +
      GlobalTheory.StdUnn.inner V x x := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_add, Matrix.mul_add, Matrix.add_mul]
  abel

theorem adj_inner (V : HSp D) (z x : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V z x) = GlobalTheory.StdUnn.inner V x z := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
    Matrix.mul_assoc]

theorem trace_inner_mul (V : HSp D) (b : Mx D n n) (z x : Mx D V.rank n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b)) = Matrix.trace (b * GlobalTheory.StdUnn.inner V z x) := by
  rw [Matrix.trace_mul_comm b]
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    Matrix.trace (b * GlobalTheory.StdUnn.inner V x z) = cA D (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x)) := by
  rw [← GlobalTheory.MixModel.trace_adj, GlobalTheory.MixModel.adj_mul, GlobalTheory.CompanionTheory.EisCovar.Unip.adj_inner, hb,
    Matrix.trace_mul_comm]

theorem quad_shift (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V (z + x) (z + x))) =
      halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V z z)) + trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b))) +
        halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V x (x ⬝ b))) := by
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.inner_add_add, GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul,
    GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul]
  simp only [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add']
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.trace_swap V hb z x,
    ← GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add_cA (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x))]
  abel

theorem mat_inv_unip {g : G D n} {b : Mx D n n} (hg : mat g = blk4 1 b 0 1) : mat g⁻¹ = blk4 1 (-b) 0 1 := by
  have h1 : GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1 = 1 := by
    rw [hg, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      neg_add_cancel, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  calc GlobalTheory.StdUnn.mat g⁻¹ = GlobalTheory.StdUnn.mat g⁻¹ * (GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1) := by
        rw [h1, Matrix.mul_one]
    _ = GlobalTheory.StdUnn.blk4 1 (-b) 0 1 := by
        rw [← Matrix.mul_assoc, GlobalTheory.CompanionTheory.EisCovar.mat_inv_mul', Matrix.one_mul]

end GlobalTheory.CompanionTheory.EisCovar.Unip

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_unip : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g b hb hg
  unfold GlobalTheory.CompanionTheory.EisCovar.CovAt
  intro v Φ Ψ hΨ
  have hinv := GlobalTheory.CompanionTheory.EisCovar.Unip.mat_inv_unip hg
  funext z
  rw [hinv, hW.unip g b hg Ψ z, hΨ]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [GlobalTheory.CompanionTheory.EisCovar.x_part_mul_block, GlobalTheory.CompanionTheory.EisCovar.y_part_mul_block]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_neg]
  rw [hW.unip g b hg Φ, GlobalTheory.CompanionTheory.EisCovar.Unip.quad_shift V hb z (xPart v)]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.mul_neg,
    Matrix.trace_add, Matrix.trace_neg, map_add, map_neg]
  ring

end GlobalTheory.CompanionTheory.EisCovar
