import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_haar_fundamental_domain_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∃ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ ∧ μ 𝓕 = 1 ∧
      (∀ Φ ∈ PolData B G.M, ∀ h, IntegrableOn (fun u : unip σ G.W H' => G.M.I om Φ (u.1 * h)) 𝓕 μ) ∧
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, IntegrableOn (fun u : unip σ G.W H' => G.M'.I om' Φ' (u.1 * h)) 𝓕 μ := by
  first | exact @GlobalTheory.ThK.CtInt.exists_domain_integrableOn | exact GlobalTheory.ThK.CtInt.exists_domain_integrableOn | (intros; apply GlobalTheory.ThK.CtInt.exists_domain_integrableOn <;> assumption)
