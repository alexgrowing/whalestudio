import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coset_sum_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ φ : GLw n w → ℂ, (∀ g, ∀ k ∈ K', φ (g * k) = φ g) → HasCompactSupport φ → hint (GlobalTheory.LFun.KGL w n) φ = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m => hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
  first | exact @GlobalTheory.CompanionTheory.IntDec.integral_decomposition | exact GlobalTheory.CompanionTheory.IntDec.integral_decomposition | (intros; apply GlobalTheory.CompanionTheory.IntDec.integral_decomposition <;> assumption)
