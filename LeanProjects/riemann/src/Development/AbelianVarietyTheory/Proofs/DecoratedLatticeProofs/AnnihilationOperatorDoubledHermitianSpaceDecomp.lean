import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnDec

theorem mul_split {b n k : ℕ} (W : Matrix (Fin b) (Fin (n + n)) ℂ) (N : Matrix (Fin (n + n)) (Fin k) ℂ) :
    W * N = W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inl i)) id
      + W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add]

theorem annih_dec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (μ : D.host.E), IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ), ∃ (X X' : Matrix (Fin B.rank) (Fin A.rank) ℂ) (c : ℂ), ∀ f, IsThetaFunO ψ (dblSp A) B f → annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) Y f = annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f + c • annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X' * (dblDec A).qX.map (tauE D τ)) f := by
  intro D ψ hψ θ hθ A B μ hμ s' sB hs hsB τ Y
  have hLine : LineAtExists D := fun θ hθ m n τ z => ⟨_, GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z⟩
  obtain ⟨hadd, hsm, -⟩ := Formalism.IndefR.Fock.DRho.dRhoLin D ψ θ hψ hθ hLine (dblSp A) B τ
  have hs2 : s' τ * s' τ = 1 := (GlobalTheory.CartStd.isCartanInv_stdInv D A μ hμ s' hs τ).1
  have hB2 : sB τ * sB τ = 1 := (hsB τ).1

  obtain ⟨-, hdet, hinv⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hMN : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have htop : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      (dblDec A).qX.map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hbot : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id =
      (μ⁻¹ • (dblDec A).qY).map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  set q := (dblDec A).qX.map (tauE D τ) with hq
  set k : ℂ := (tauE D τ μ)⁻¹ * (‖tauE D τ μ‖ : ℂ) with hk
  have hqs := GlobalTheory.StdUnnAnnih.qX_mul_stdInv A μ hμ s' hs τ
  have hbot' : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) = k • (q * s' τ) := by
    rw [hqs, smul_smul, hk, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  set W := Y * (Tm A μ).map (tauE D τ) with hW
  set P := W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) with hP
  set R := W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) with hR
  have hYd : Y = P * q + R * (k • (q * s' τ)) := by
    have h1 : Y = W * ((Tm A μ)⁻¹).map (tauE D τ) := by rw [hW, Matrix.mul_assoc, hMN, Matrix.mul_one]
    rw [h1, mul_split, htop, hbot, hbot']
  refine ⟨P, (-Complex.I * k) • (sB τ * R), -Complex.I, fun f hf => ?_⟩
  set J := cplxO (s' τ) (sB τ) with hJ
  have hJadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (Z + Z') = J Z + J Z' := by
    intro Z Z'
    simp only [hJ, cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hJJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (J Z) = -Z := by
    intro Z
    simp only [hJ, cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    simp only [Matrix.mul_assoc]
    rw [hs2, ← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul, Matrix.mul_one, neg_one_smul]
  have hneg : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      dRho (heisO ψ (dblSp A) B) θ τ (-Z) f = -dRho (heisO ψ (dblSp A) B) θ τ Z f := by
    intro Z
    have h := hsm (-1) Z f hf
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul] at h
    exact h
  have hAadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (Z + Z') f =
        annih (heisO ψ (dblSp A) B) θ τ J Z f + annih (heisO ψ (dblSp A) B) θ τ J Z' f := by
    intro Z Z'
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJadd, hadd _ _ f hf, hadd _ _ f hf, smul_add]
    abel
  have hAJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (J Z) f = (-Complex.I) • annih (heisO ψ (dblSp A) B) θ τ J Z f := by
    intro Z
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJJ, hneg]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (dRho (heisO ψ (dblSp A) B) θ τ (J Z) f x) * Complex.I_sq
  have hdir : J (((-Complex.I * k) • (sB τ * R)) * q) = R * (k • (q * s' τ)) := by
    have hc : Complex.I * (-Complex.I * k) = k := by linear_combination (-k) * Complex.I_sq
    simp only [hJ, cplxO, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul]
  rw [hYd, ← hdir, hAadd, hAJ]

end GlobalTheory.StdUnnAnnDec
