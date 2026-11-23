import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConstantTermIntegral
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
theorem _root_.GlobalTheory.T.levi_constant_term_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (γ : UA σ W₁.J) (m : UA σ W.J),
    m ∈ ratU σ W.J → IsLevi H 1 γ m → ∀ Φ : UA σ W.J → ℂ,
    (∀ δ ∈ ratU σ W.J ⊓ unip σ W H, ∀ u ∈ unip σ W H, Φ (δ * u) = Φ u) →
    ∀ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ → μ 𝓕 = 1 →
      ∫ u in 𝓕, Φ (m * u.1 * m⁻¹) ∂μ = ∫ u in 𝓕, Φ u.1 ∂μ := by
  first | exact @GlobalTheory.UnipCT.setIntegral_conj_levi_of_unip_invariant | exact GlobalTheory.UnipCT.setIntegral_conj_levi_of_unip_invariant | (intros; apply GlobalTheory.UnipCT.setIntegral_conj_levi_of_unip_invariant <;> assumption)
