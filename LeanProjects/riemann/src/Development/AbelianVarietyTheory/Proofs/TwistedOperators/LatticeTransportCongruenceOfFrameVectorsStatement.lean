import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTransport_congruence_of_frameVectors : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  first | exact @GlobalTheory.LevCong.cong_of_frame | exact GlobalTheory.LevCong.cong_of_frame | (intros; apply GlobalTheory.LevCong.cong_of_frame <;> assumption)
