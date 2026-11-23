import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecayStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.ThKSmallLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem so_le_schA {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {v : Pl F} (t : E →ₐ[F] Fv F v) : M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem theta_add_smul {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ}
    {χ χ' : Chr F E} {om : Rep σ Y W} (hw : M.IsWeil ψ χ χ' om) {Φ Ψ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (c : ℂ) (g : UA σ Y.J) (h : UA σ W.J) :
    theta om (Φ + c • Ψ) g h = theta om Φ g h + c * theta om Ψ g h := by
  have hS := IsUWeilPair.isUSplitting hw
  obtain ⟨l, -, hl⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  simp only [theta]
  rw [← hl _ (hS.pres _ _ hΦ), ← hl _ (hS.pres _ _ hΨ),
    ← hl _ (hS.pres _ _ (Submodule.add_mem _ hΦ (Submodule.smul_mem _ c hΨ))), map_add, map_smul, map_add, map_smul,
    smul_eq_mul]

theorem smallI_add_smul : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, ∀ (c : ℂ) (h : UA σ G.W.J),
      G.M'.I om' (Φ + c • Ψ) h = G.M'.I om' Φ h + c * G.M'.I om' Ψ h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT Φ hΦ Ψ hΨ c h
  have hD : Decay B G om om' := GlobalTheory.T.theta_kernel_decay hP F E σ B a a' G X om om' hT
  have i1 := (hD.2 Φ hΦ).2.1 h
  have i2 := (hD.2 Ψ hΨ).2.1 h
  have e := fun g => theta_add_smul hT.weil' (so_le_schA hT.geo.hM' _ hΦ) (so_le_schA hT.geo.hM' _ hΨ) c g h
  unfold Model.I
  simp only [e]
  rw [integral_add i1 (i2.const_mul c), integral_const_mul]

end GlobalTheory.ThKSmallLin

end
