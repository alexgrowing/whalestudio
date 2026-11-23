import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactFrameEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_frame_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | exact GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff <;> assumption)
