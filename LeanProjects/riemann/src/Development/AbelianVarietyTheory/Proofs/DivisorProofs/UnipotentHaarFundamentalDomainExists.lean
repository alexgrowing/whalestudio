import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaIntegralContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCompactFundamentalSetStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.CtInt

local instance topRingAE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem integrableOn_of_invariant {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {S : Subgroup (UA σ J)} {Γ : Subgroup S}
    {f : S → ℂ} (hf : Continuous f) (hinv : ∀ γ ∈ Γ, ∀ u, f (γ * u) = f u)
    {K : Set S} (hK : IsCompact K) (hcov : ∀ u : S, ∃ γ ∈ Γ, γ * u ∈ K)
    (μ : Measure S) {s : Set S} (hs : μ s ≠ ⊤) : IntegrableOn f s μ := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine Measure.integrableOn_of_bounded (M := C) hs hf.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  obtain ⟨γ, hγ, hγu⟩ := hcov u
  rw [← hinv γ hγ u]
  exact hC _ hγu

theorem exists_domain_integrableOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∃ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ ∧ μ 𝓕 = 1 ∧
      (∀ Φ ∈ PolData B G.M, ∀ h, IntegrableOn (fun u : unip σ G.W H' => G.M.I om Φ (u.1 * h)) 𝓕 μ) ∧
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, IntegrableOn (fun u : unip σ G.W H' => G.M'.I om' Φ' (u.1 * h)) 𝓕 μ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.T.unipotent_compact_fundamental_set F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨c1, c2⟩ := GlobalTheory.T.pol_data_theta_integral_continuous hKP F E σ B a a' G X om om' hT
  obtain ⟨r1, r2⟩ := GlobalTheory.T.theta_lift_left_invariant hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hfin : μ 𝓕 ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  refine ⟨μ, 𝓕, hμ, hF, h1, ?_, ?_⟩
  · intro Φ hΦ h
    refine integrableOn_of_invariant (K := K) ?_ ?_ hK hcov μ hfin
    · exact (c1 Φ hΦ).comp ((continuous_mul_const h).comp continuous_subtype_val)
    · intro γ hγ u
      have hγ' : (γ : UA σ G.W.J) ∈ ratU σ G.W.J := Subgroup.mem_subgroupOf.mp hγ
      show G.M.I om Φ ((γ : UA σ G.W.J) * u.1 * h) = G.M.I om Φ (u.1 * h)
      rw [mul_assoc]; exact r1 Φ hΦ _ hγ' _
  · intro Φ hΦ h
    refine integrableOn_of_invariant (K := K) ?_ ?_ hK hcov μ hfin
    · exact (c2 Φ hΦ).comp ((continuous_mul_const h).comp continuous_subtype_val)
    · intro γ hγ u
      have hγ' : (γ : UA σ G.W.J) ∈ ratU σ G.W.J := Subgroup.mem_subgroupOf.mp hγ
      show G.M'.I om' Φ ((γ : UA σ G.W.J) * u.1 * h) = G.M'.I om' Φ (u.1 * h)
      rw [mul_assoc]; exact r2 Φ hΦ _ hγ' _

end GlobalTheory.ThK.CtInt
