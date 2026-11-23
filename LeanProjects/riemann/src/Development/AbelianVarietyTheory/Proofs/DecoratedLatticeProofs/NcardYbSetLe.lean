import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosetsS

theorem ncard_ybSet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ n ≤ N.Nm, (((ybSet sel mu cst (Formalism.L2.Col.stdLat X.E n)).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E L → ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H n hn
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, hmu, -⟩ := H
  have hf : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.ok.rankE, ← hX.ok.card_Tau, mul_comm]
    rfl
  have key : ∀ L : Submodule (𝓞 X.E) (Sp X.E n), ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (2 * errUnit N (Pr.T u)) := by
    intro L
    have h1 := (GlobalTheory.CouplingCosets.finite_ncard_ybSet hPr sel mu hmu cst L).2
    rw [hf, hg 0, hg 1] at h1
    have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
    have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
    have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
    have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
    have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
    have he : 2 * N.R.f * n ≤ 2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) := by
      refine Nat.mul_le_mul_left _ (hn.trans ?_)
      have hm : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by have := N.R.two_le_m; omega)
      calc N.Nm ≤ N.Nm ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ N.R.m ^ 2 * N.Nm ^ 2 := Nat.le_mul_of_pos_left _ hm
    calc ((ybSet sel mu cst L).ncard : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (2 * N.R.f * n) := by exact_mod_cast h1
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * n) := pow_le_pow_left₀ (by linarith) ggT _
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
      _ = Real.exp (2 * errUnit N (Pr.T u)) := by
        rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
        unfold errUnit
        push_cast
        ring
  exact ⟨key _, fun L _ => key L⟩

end GlobalTheory.CouplingCosetsS
