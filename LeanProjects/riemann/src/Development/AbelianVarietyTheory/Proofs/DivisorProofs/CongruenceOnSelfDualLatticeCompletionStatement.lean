import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeCompletion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_on_selfDual_lattice_completion : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  first | exact @GlobalTheory.LatHatCong.cong_on_hat | exact GlobalTheory.LatHatCong.cong_on_hat | (intros; apply GlobalTheory.LatHatCong.cong_on_hat <;> assumption)
