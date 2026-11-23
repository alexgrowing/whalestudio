import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormChangeOfBasisLie
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_automorphic_invariance : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (N : Subgroup (GA D V)) (N₁ : Subgroup (GA D V')), (∀ p ∈ N, ∀ a ∈ unip D.sp.cm.sig V.gram X T, p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → (∀ v ∈ N, ∃ u ∈ N₁, v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → ∃ π : N →* N₁, Continuous π ∧ (∀ (v : N) (u : N₁), π v = u ↔ (v : GA D V) * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) ∧ ∀ v : N, (v : GA D V) ∈ GQ V → (π v : GA D V') ∈ GQ V' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj <;> assumption)
