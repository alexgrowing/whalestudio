import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {R : Type} [CommRing R] {n ρ p : ℕ}

theorem lr_bl_mul (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem lr_bl_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn))
    (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem lr_exists_bl (hn : ρ + p = n) (T : Matrix (Fin n) (Fin n) R) :
    ∃ (T₁₁ : Matrix (Fin ρ) (Fin ρ) R) (T₁₂ : Matrix (Fin ρ) (Fin p) R)
      (T₂₁ : Matrix (Fin p) (Fin ρ) R) (T₂₂ : Matrix (Fin p) (Fin p) R),
      T = bl hn T₁₁ T₁₂ T₂₁ T₂₂ := by
  let M := T.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₁, M.toBlocks₂₂, ?_⟩
  simp only [bl, Matrix.fromBlocks_toBlocks, M, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem lr_eq_zero {m : ℕ} (a b c d : Matrix (Fin p) (Fin p) R) (hy : IsUnit (blk4 a b c d).det)
    (X : Matrix (Fin m) (Fin p) R) (hc : X * c = 0) (hd : X * d = 0) : X = 0 := by
  have hF : IsUnit (Matrix.fromBlocks a b c d).det := by
    have h := hy
    simp only [blk4] at h
    rwa [Matrix.det_submatrix_equiv_self] at h
  have hRF : Matrix.fromCols (0 : Matrix (Fin m) (Fin p) R) X * Matrix.fromBlocks a b c d = 0 := by
    ext i (j | j)
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type] using congrFun (congrFun hc i) j
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type] using congrFun (congrFun hd i) j
  have hR : Matrix.fromCols (0 : Matrix (Fin m) (Fin p) R) X = 0 := by
    have h := congrArg (· * (Matrix.fromBlocks a b c d)⁻¹) hRF
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF] using h
  ext i j
  simpa using congrFun (congrFun hR i) (Sum.inr j)

end GlobalTheory.CompanionTheory.ZUnf.LowerRows

namespace GlobalTheory.CompanionTheory.ZUnf

open GlobalTheory.CompanionTheory.ZUnf.LowerRows in

theorem lowerRows_determine : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ : Matrix (Fin p) (Fin p) K) (ζ ζ₂ : Matrix (Fin ρ) (Fin ρ) K)
      (η η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
    rowC hn η₂ a₂ c₂ = T * rowC hn η a c → rowD hn σ ζ₂ η₂ b₂ d₂ = T * rowD hn σ ζ η b d →
    (∃ T' : Matrix (Fin p) (Fin p) K, c₂ = T' * c ∧ d₂ = T' * d) ∧
    (IsUnit (blk4 a b c d).det → a₂ = a → b₂ = b → c₂ = c → d₂ = d → ζ₂ = ζ ∧ η₂ = η) := by
  intro K _ σ _ n ρ p hn a b c d a₂ b₂ c₂ d₂ ζ ζ₂ η η₂ T h₁ h₂
  obtain ⟨T₁₁, T₁₂, T₂₁, T₂₂, rfl⟩ := lr_exists_bl hn T
  simp only [rowC, rowD, lr_bl_mul] at h₁ h₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := lr_bl_inj hn h₁
  obtain ⟨f₁, f₂, f₃, f₄⟩ := lr_bl_inj hn h₂
  have hT₁₁ : T₁₁ = 1 := by
    simpa using e₁.symm
  have hT₂₁ : T₂₁ = 0 := by
    simpa using e₃.symm
  subst hT₁₁ hT₂₁
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_neg, zero_add, add_zero,
    neg_zero] at e₂ e₄ f₁ f₂ f₃ f₄
  refine ⟨⟨T₂₂, e₄, f₄⟩, ?_⟩
  intro hy ha hb hc hd
  subst ha hb hc hd
  have hT₂₂ : T₂₂ = 1 := by
    have h0 : T₂₂ - 1 = 0 := by
      refine lr_eq_zero a₂ b₂ c₂ d₂ hy (T₂₂ - 1) ?_ ?_
      · rw [Matrix.sub_mul, Matrix.one_mul, ← e₄, sub_self]
      · rw [Matrix.sub_mul, Matrix.one_mul, ← f₄, sub_self]
    exact sub_eq_zero.1 h0
  subst hT₂₂
  have hη : η₂ = η := by
    have h := neg_injective (by simpa using f₃ : -cT σ η₂ = -cT σ η)
    ext i j
    have := congrFun (congrFun h j) i
    exact σ.injective (by simpa [cT] using this)
  subst hη
  have hT₁₂ : T₁₂ = 0 := by
    refine lr_eq_zero a₂ b₂ c₂ d₂ hy T₁₂ ?_ ?_
    · simpa using e₂
    · simpa using f₂
  subst hT₁₂
  refine ⟨?_, rfl⟩
  simpa using f₁

end GlobalTheory.CompanionTheory.ZUnf
