import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerThetaStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB

namespace GlobalTheory.ConeSoB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cone_mem_So (hP : GlobalTheory.FunPr.Hypotheses₂) (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)) (hC : CfgB B G G₁ H H') (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b))
    (he' : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e') (K : Subgroup (UA σ G.V'.J)) (μK : Measure K)
    (μ : Measure (AE F E)ˣ) (hK : IsStab B K) (hμK : μK.IsHaarMeasure) (hμ : μ.IsHaarMeasure) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') :
    ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, IntOK B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ' ∧
      cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ' ∈ G₁.M'.So B.ψ B.τ₁ := by
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he'.loc
  intro Φ' hΦ'
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hφ, hvac, hso, rfl⟩ := hx
    obtain ⟨hI, c, f₁, ψ, μK₁, μ₁, hK₁, hμ₁, hψ, hψv, hψ1, hcone⟩ :=
      GlobalTheory.T.config_b_stabilizer_eigen hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μK μ hμK hμ f φ hφ hvac
    refine ⟨hI, ?_⟩
    rw [hcone]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨f₁, ψ, hψ, hψv, ?_, rfl⟩)
    rw [hψ1]
    exact GlobalTheory.T.config_b_stabilizer_theta B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μK₁ μ₁ hK₁ hμ₁ _ hso
  | zero =>
    refine ⟨intOK_zero, ?_⟩
    have h := (intOK_lin (B := B) (M := G.M') (om := om') (e := e') (K := K) (μK := μK) (μ := μ) (u := shiftB σ H H')
      (ν := X.ν) (z := (a - (b + 2)) / 2 + 1) 0 0 intOK_zero intOK_zero).2
    simp only [zero_smul, add_zero] at h
    rw [h]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have h := intOK_lin 1 1 hx.1 hy.1
    simp only [one_smul] at h
    rw [h.2]
    exact ⟨h.1, add_mem hx.2 hy.2⟩
  | smul c x _ hx =>
    have h := intOK_lin c 0 hx.1 hx.1
    simp only [zero_smul, add_zero] at h
    rw [h.2]
    exact ⟨h.1, Submodule.smul_mem _ c hx.2⟩

end GlobalTheory.ConeSoB
