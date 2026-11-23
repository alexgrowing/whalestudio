import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaAdditiveStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKKill

open Classical in

theorem kill : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ φ' : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M'.Pol B.ψ B.emb →
      (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ' B.v₁ ∈ SB _ → (∀ v, v ≠ B.v₁ → φ' v = φ v) →
      φ B.v₁ - φ' B.v₁ ∈ augAt om' B.v₁ → G.M'.I om' (pure f φ') = G.M'.I om' (pure f φ) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT hq f φ φ' hf hSB hvac hφ'1 hφ' hD
  classical
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hT.geo.hM'.std).mono fun v h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor B.v₁ f φ hstd
  let P : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) → (Fin a' × Fin (a + a') → AF F) → ℂ :=
    fun χ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ χ)
  have hPt : ∀ χ, P χ = tens (evFin F B.v₁) χ r := fun χ => (hrt χ).symm
  have hupd : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ v, Function.update φ B.v₁ χ v ∈ SB _ := by
    intro χ hχ v
    by_cases hv : v = B.v₁
    · subst hv; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hv]; exact hSB v
  have hPsch : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), P χ ∈ schA F _ := fun χ hχ =>
    GlobalTheory.TensUniq.pure_mem_schA f _ (hupd χ hχ) (GlobalTheory.PureFactor.update_eventually φ B.v₁ χ hstd)
  have hPpol : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), P χ ∈ PolData B G.M' := fun χ hχ =>
    Submodule.subset_span ⟨f, hf, Function.update φ B.v₁ χ, hupd χ hχ, by
      filter_upwards [hvac, Filter.eventually_cofinite_ne B.v₁] with v hv hne
      rw [Function.update_of_ne hne]; exact hv, rfl⟩
  have hPadd : ∀ χ₁ χ₂, P (χ₁ + χ₂) = P χ₁ + P χ₂ := by
    intro χ₁ χ₂; rw [hPt, hPt, hPt]; funext x; simp only [tens, Pi.add_apply]; ring
  have hPsmul : ∀ (c : ℂ) χ, P (c • χ) = c • P χ := by
    intro c χ; rw [hPt, hPt]; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  have hIsmul : ∀ (c : ℂ) Φ, G.M'.I om' (c • Φ) = c • G.M'.I om' Φ := by
    intro c Φ; funext h
    simp only [Model.I, theta, map_smul, Pi.smul_apply, smul_eq_mul]
    have e : ∀ g, thetaSum F (c • om' (g, h) Φ) = c * thetaSum F (om' (g, h) Φ) := by
      intro g; simp only [thetaSum, Pi.smul_apply, smul_eq_mul]; exact tsum_mul_left
    simp only [e]
    exact integral_const_mul c _
  let J : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) → UA σ G.W.J → ℂ := fun χ => G.M'.I om' (P χ)
  have hJadd : ∀ χ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ χ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      J (χ₁ + χ₂) = J χ₁ + J χ₂ := by
    intro χ₁ h₁ χ₂ h₂
    show G.M'.I om' (P (χ₁ + χ₂)) = G.M'.I om' (P χ₁) + G.M'.I om' (P χ₂)
    rw [hPadd]
    exact GlobalTheory.T.anisotropic_theta_additive hK F E σ B a a' G X om om' hT hq _ (hPpol χ₁ h₁) _ (hPpol χ₂ h₂)
  have hJsmul : ∀ (c : ℂ) χ, J (c • χ) = c • J χ := fun c χ => by
    show G.M'.I om' (P (c • χ)) = c • G.M'.I om' (P χ)
    rw [hPsmul, hIsmul]
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hgen : ∀ (g : UA σ G.V'.J) (ψ ψ₁ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ),
      ψ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) → Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ₁ → J ψ₁ = J ψ := by
    intro g ψ ψ₁ hψ hA
    have hRest : Rest (evFin F B.v₁) ψ r := ⟨hr, by rw [← hPt]; exact hPsch ψ hψ⟩
    have e := hA r hRest
    show G.M'.I om' (P ψ₁) = G.M'.I om' (P ψ)
    rw [hPt ψ₁, ← e, hPt ψ]
    funext h
    exact GlobalTheory.ThetaRightInv.rightInv hK.siegelSetUnitary hTB F E σ B a a' G X om om' hT hq _
      (by rw [← hPt]; exact hPsch ψ hψ) g h
  have hzero : J 0 = 0 := by
    have e : (0 : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) = (0 : ℂ) • (0 : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) :=
      (zero_smul ℂ _).symm
    rw [e, hJsmul, zero_smul]
  have hkill : ∀ z ∈ augAt om' B.v₁, z ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧ J z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, -, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩ := hx
      refine ⟨sub_mem hψ₁ hψ, ?_⟩
      have e : ψ₁ - ψ = ψ₁ + (-1 : ℂ) • ψ := by rw [neg_one_smul, sub_eq_add_neg]
      rw [e, hJadd _ hψ₁ _ ((SB _).smul_mem _ hψ), hJsmul, hgen g ψ ψ₁ hψ hA, neg_one_smul, add_neg_cancel]
    | zero => exact ⟨zero_mem _, hzero⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by rw [hJadd _ hx.1 _ hy.1, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx => exact ⟨(SB _).smul_mem c hx.1, by rw [hJsmul, hx.2, smul_zero]⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = P (φ B.v₁) := by
    show _ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (φ B.v₁)); rw [Function.update_eq_self]
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' = P (φ' B.v₁) := by
    show _ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (φ' B.v₁))
    congr 1
    funext v
    by_cases hv : v = B.v₁
    · subst hv; rw [Function.update_self]
    · rw [Function.update_of_ne hv, hφ' v hv]
  obtain ⟨hDSB, hD0⟩ := hkill _ hD
  have e3 : φ B.v₁ = φ' B.v₁ + (φ B.v₁ - φ' B.v₁) := by abel
  show G.M'.I om' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') = G.M'.I om' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)
  rw [e1, e2]
  show J (φ' B.v₁) = J (φ B.v₁)
  rw [e3, hJadd _ hφ'1 _ hDSB, hD0, add_zero]

end GlobalTheory.ThKKill

end
