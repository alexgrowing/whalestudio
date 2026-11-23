import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisConjugateZeroEntries
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_basis_block_entries : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (l d : ℕ), l + d ≤ m →
    (∃ k ∈ T, k.val + 1 = l + d) → (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A ∈ lieAt V τ →
    (∀ a b : Fin V.rank, ((C.1.map (tauE D τ))⁻¹ * A * C.1.map (tauE D τ)) a b ≠ 0 →
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val) →
    ∀ t : ℝ, oneP θ V τ A t ∈ unip D.sp.cm.sig V.gram X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UnipOne.oneP_mem_unip | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UnipOne.oneP_mem_unip | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UnipOne.oneP_mem_unip <;> assumption)
