import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLineLeviEigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaNonvanishingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem actsD_zero_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem eq_zero_of_pGen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)} (hC : CfgB B G G₁ H H') {X : Chars F E} (hX : IsHecke F E X.β)
    {om : Rep σ G.V G.W} {om₁ : Rep σ G₁.V G₁.W} {R : RealMaps F a (b + 2)} {R₁ : RealMaps F a b}
    {φ : R.Pi →ₗ[ℂ] R₁.Pi} (hφ : IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ)
    {V : Submodule ℂ R.Pi} (hG : PGen B G.M om R.p G₁.W H' V) (h0 : ∀ v ∈ V, φ v = 0) : φ = 0 := by
  have hN := hG (LinearMap.ker φ) (fun v hv => LinearMap.mem_ker.2 (h0 v hv))
    (fun γ hγ hu f hf f₁ h1 _ => LinearMap.mem_ker.2 (hφ.unip γ hγ hu f hf f₁ h1))
    (fun γ hγ ⟨t, γ₁, hγ₁, hL⟩ f hf f₁ h1 hpf => by
      obtain ⟨c, hc⟩ := GlobalTheory.T.hecke_line_levi_eigenvalue F E σ B _ _ G.W G₁.W H' _ _ hC.hH' X.β hX ((a : ℝ) / 2) γ hγ γ₁ t hL
      have e := hφ.lie γ hγ γ₁ hγ₁ t hL f hf f₁ h1 0 (zero_mem _) 0
        (actsD_zero_zero (fun s => om₁ (1, γ₁ (Multiplicative.ofAdd s))))
        (by rw [LinearMap.mem_ker.1 hpf, map_zero]) c hc
      rw [LinearMap.mem_ker.1 hpf, map_zero, smul_zero, add_zero] at e
      exact LinearMap.mem_ker.2 e)
  exact LinearMap.ker_eq_top.1 hN

theorem indLineInf_beta_of_isMatched : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      IndLineInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ φ φ' hφ hφ'
  obtain ⟨V, hV0, hVK, hV⟩ := GlobalTheory.T.config_b_theta_nonvanishing hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hG := GlobalTheory.T.config_b_theta_unfolding hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ V hV0 hVK
  have hX : IsHecke F E X.β := hM.triple.chars.heckeβ
  rcases hV φ φ' hφ hφ' with h0 | ⟨c, hc⟩
  · exact Or.inl (eq_zero_of_pGen hC hX hφ hG h0)
  · refine Or.inr ⟨c, ?_⟩
    have e := eq_zero_of_pGen hC hX
      (GlobalTheory.T.config_b_theta_integrability hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ φ φ' hφ hφ' c) hG
      (fun v hv => by rw [LinearMap.sub_apply, LinearMap.smul_apply, hc v hv, sub_self])
    exact sub_eq_zero.1 e

end GlobalTheory.IndLine
