import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEpsilonCentralizerBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_epsilon_centralizer_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = v ᵥ* aeval γ h) → ∀ e : Matrix (Fin n) (Fin n) K, IsPrim γ e → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n, g.val * γ.map (algebraMap K (AdeleRing (𝓞 K) K)) = γ.map (algebraMap K (AdeleRing (𝓞 K) K)) * g.val → ∀ s : (AdeleRing (𝓞 K) K)ˣ, (s : AdeleRing (𝓞 K) K) = (1 + e.map (algebraMap K (AdeleRing (𝓞 K) K)) * (g.val - 1)).det → c ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) → ∀ x : Fin n → K, x ᵥ* e ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height g x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | exact GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | (intros; apply GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height <;> assumption)
