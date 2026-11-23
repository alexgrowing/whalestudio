import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationIntertwinesThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorFixesIntegralIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionRestrictedProductStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ShiftSupport

theorem rho_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (hφ : ∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    M.co.rho ψ u (pure f φ) = pure (locOpInf (M.co.rho ψ (partInf F u)) f) (fun v => locOp v (M.co.rho ψ (partFin v u)) (φ v)) ∧
      ∀ᶠ v in cofinite, locOp v (M.co.rho ψ (partFin v u)) (φ v) = φ v := by
  refine ⟨GlobalTheory.T.weil_action_restricted_product M ψ hψ u f φ hφ hstd, ?_⟩
  filter_upwards [GlobalTheory.T.local_operator_fixes_integral_indicator M ψ hψ u, hstd] with v h1 h2
  rw [h2, h1]

theorem shifted_mem_So : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h,
        ∀ (k : K) (l : (AE F E)ˣ), e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) ∈ G₁.M'.So B.ψ B.τ₁ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h k l
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he'.loc
  obtain ⟨ι₁, hι₁, hrank⟩ := GlobalTheory.T.config_b_evaluation_intertwines_theta B G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc
  have hS : om' (k.1, h) Φ' ∈ G.M'.So B.ψ B.τ₁ :=
    GlobalTheory.T.weil_representation_preserves_space hKP.base F E σ B a (b + 2) G X om om' hT (k.1, h) Φ' (Submodule.mem_inf.1 hΦ').2
  let R : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F (b + 2) (a + (b + 2)) :=
    { toFun := G.M'.co.rho B.ψ (shiftB σ H H' l)
      map_add' := fun f g => funext fun x => mul_add _ _ _
      map_smul' := fun c f => funext fun x => mul_left_comm _ _ _ }
  suffices hle : G.M'.So B.ψ B.τ₁ ≤ (G₁.M'.So B.ψ B.τ₁).comap (e'.comp R) from hle hS
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, hφ, hvac, hso, rfl⟩
  have hstd := hT.geo.hM'.std
  obtain ⟨hpure, hae⟩ := rho_pure G.M' B.ψ hT.base.std (shiftB σ H H' l) f φ hφ
    ((hvac.and hstd).mono fun v hv => hv.1.trans hv.2)
  rw [SetLike.mem_coe, Submodule.mem_comap]
  change e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (pure f φ)) ∈ G₁.M'.So B.ψ B.τ₁
  rw [hpure, hloc _ _ (fun v => locOp_mem _ _ _) (by filter_upwards [hae, hvac] with v h1 h2; rw [h1, h2])]
  refine Submodule.subset_span ⟨_, fun v => ev v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (φ v)),
    fun v => ?_, ?_, ?_, rfl⟩
  · rw [← (hev v).2]; exact Submodule.mem_map_of_mem (locOp_mem _ _ _)
  · filter_upwards [hae, hvac] with v h1 h2
    rw [h1, h2, (hev v).1]
  · refine ⟨?_, ι₁, hι₁, fun Y hY => hrank _ hso l Y hY⟩
    rw [← (hev B.v₁).2]; exact Submodule.mem_map_of_mem (locOp_mem _ _ _)

end GlobalTheory.ShiftSupport

end
