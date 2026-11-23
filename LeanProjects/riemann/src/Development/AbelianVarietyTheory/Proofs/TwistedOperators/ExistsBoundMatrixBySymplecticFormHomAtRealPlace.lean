import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymplBound

theorem symplAt_pick {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (i : Fin T.rank) (j : Fin S.rank) (w : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ
      (((tauE D τ D.host.xi0)⁻¹ * w) • ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ)) X =
      2 * (w * starRingEnd ℂ (X i j)).re := by
  have hc : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hT := GlobalTheory.SmoothAutCheck.gramAt_unit T τ
  have hS := GlobalTheory.SmoothAutCheck.gramAt_unit S τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  congr 2
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have e1 : (gramAt D S τ)⁻¹ * Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j (1 : ℂ) * gramAt D S τ) =
      (gramAt D S τ)⁻¹ * (Xᴴ * Matrix.single i j (1 : ℂ)) * gramAt D S τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (gramAt D T τ), mul_nonsing_inv _ hT, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ hS, Matrix.one_mul,
    Matrix.trace_mul_single]
  simp only [Matrix.conjTranspose_apply, MulOpposite.op_one, one_smul, Complex.star_def]
  field_simp

theorem bound : ∀ (D : D7) (S T : HSp D) (τ : D.what₂.Tau), ∃ (n : ℕ) (zs : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ) (κ : ℝ), ∀ X : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∑ i, ∑ j, ‖X i j‖ ≤ κ * ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs l) X| := by
  intro D S T τ
  let g : Fin 2 × Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun p =>
    ((tauE D τ D.host.xi0)⁻¹ * Complex.I ^ (p.1 : ℕ)) •
      ((gramAt D T τ)⁻¹ * Matrix.single p.2.1 p.2.2 (1 : ℂ) * gramAt D S τ)
  let e := Fintype.equivFin (Fin 2 × Fin T.rank × Fin S.rank)
  refine ⟨_, fun l => g (e.symm l), 1, fun X => ?_⟩
  rw [one_mul, Equiv.sum_comp e.symm (fun p => |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (g p) X|),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  simp only [g, symplAt_pick, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
  have h1 : (starRingEnd ℂ (X i j)).re = (X i j).re := Complex.conj_re _
  have h2 : (Complex.I * starRingEnd ℂ (X i j)).re = (X i j).im := by simp
  rw [h1, h2, abs_mul, abs_mul, abs_two]
  have := Complex.norm_le_abs_re_add_abs_im (X i j)
  nlinarith [abs_nonneg (X i j).re, abs_nonneg (X i j).im]

end GlobalTheory.SymplBound
