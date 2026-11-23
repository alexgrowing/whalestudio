import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReconfiguredTripleCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reconfigured_triple_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    (∀ γ ∈ ratU σ G₁.W.J, emb γ ∈ ratU σ G.W.J) ∧
    (∀ c : E, w * nn (inclR (F := F) (AF F) c) ∈ ratU σ G.W.J) ∧
    (∀ c c' : E, GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) c) * (w * nn (inclR (F := F) (AF F) c'))⁻¹) → c = c') ∧
    (∀ δ ∈ ratU σ G.W.J ⊓ unip σ G.W H', ∃ a₀ : E, ∀ c : E,
      GlobalTheory.ConeSmallSer.StabLn H'.x (w * nn (inclR (F := F) (AF F) c) * δ * (w * nn (inclR (F := F) (AF F) (c + a₀)))⁻¹)) := by
  first | exact @GlobalTheory.SwapShearLines.swap_shear_lines | exact GlobalTheory.SwapShearLines.swap_shear_lines | (intros; apply GlobalTheory.SwapShearLines.swap_shear_lines <;> assumption)
