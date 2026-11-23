import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalZeroStatement

open scoped TensorProduct NNReal Matrix SchwartzMap
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvCompNe

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_sub {κ : Type} [Fintype κ] (f f' : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - f') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.sub_apply, Pi.sub_apply, sub_mul]

theorem eq_of_pure_eq {κ : Type} [Fintype κ] {f f' : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ}
    (h0 : ∀ v, φ v ≠ 0) (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ) : f = f' := by
  by_contra hne
  exact GlobalTheory.ThK.EvNeZero.pure_ne_zero (f - f') (sub_ne_zero.2 hne) φ h0 hstd (by rw [pure_sub, h, sub_self])

theorem exists_schrF {κ : Type} [Fintype κ]
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, ⇑f₁ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ) w ⇑f := by
  refine ⟨GlobalTheory.HeisSchA.archS f w.2 w.1 (GlobalTheory.ArchUniq.trP F κ w.1 w.2 / 2), ?_⟩
  funext y
  rw [GlobalTheory.HeisSchA.archS_apply, GlobalTheory.Published.Metaplectic.eChar_apply, GlobalTheory.ArchUniq.schrF, ContinuousLinearMap.neg_apply,
    GlobalTheory.HeisSchA.trL_apply]
  congr 2
  simp only [GlobalTheory.ArchUniq.trP, dotProduct]
  push_cast
  ring

theorem lift_at {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) (u : AF F) (hu : evI F u = 0) :
    u • GlobalTheory.ArchUniq.liftV y = 0 := by
  have h1 : GlobalTheory.ArchUniq.liftV y = realAd F 1 • GlobalTheory.ArchUniq.liftV y := by
    conv_lhs => rw [← GlobalTheory.ArchUniq.Coord.loc_lift y]
    exact GlobalTheory.ArchUniq.Coord.lift_loc _
  rw [h1, smul_smul, GlobalTheory.ArchUniq.Coord.mul_realAd_eq_zero u hu, zero_smul]

end GlobalTheory.ThK.EvCompNe

namespace GlobalTheory.ThK.EvCompNe

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem range_stable {B : Base F E} (hB : B.IsGood σ) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
    {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ ι ι' I e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (hv : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hl : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v))
    (f : SInf F (Fin n × Fin d))
    (w : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) × (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F))
    (g₁ : SInf F (Fin n₁ × Fin d₁)) (hg₁ : ⇑g₁ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F _) w ⇑(ei f)) :
    ∃ f₁, ei f₁ = g₁ := by
  set z := M₁.co.e.symm (GlobalTheory.ArchUniq.liftV w.1, GlobalTheory.ArchUniq.liftV w.2) with hz
  have hze : M₁.co.e z = (GlobalTheory.ArchUniq.liftV w.1, GlobalTheory.ArchUniq.liftV w.2) := by
    rw [hz, LinearEquiv.apply_symm_apply]
  have hzat : At (evI F) z := by
    intro u hu
    rw [hz, ← LinearEquiv.map_smul, Prod.smul_mk, lift_at _ u hu, lift_at _ u hu]
    exact map_zero _
  set z' := incM F ι * z * (incM F ι')ᵀ with hz'
  have hz'at : At (evI F) z' := by
    intro u hu
    rw [hz', ← Matrix.smul_mul, ← Matrix.mul_smul, hzat u hu, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨f₁, hf₁⟩ := exists_schrF (GlobalTheory.ArchUniq.locV (M.co.e z').1, GlobalTheory.ArchUniq.locV (M.co.e z').2) f
  refine ⟨f₁, ?_⟩
  have hA := GlobalTheory.ArchUniq.acts_rho_of_at_inf B.ψ hB.std M.co z' hz'at f f₁ hf₁
  have hA₁ := GlobalTheory.ArchUniq.acts_rho_of_at_inf B.ψ hB.std M₁.co z hzat (ei f) g₁ (by
    rw [hg₁, hze, GlobalTheory.ArchUniq.Coord.loc_lift, GlobalTheory.ArchUniq.Coord.loc_lift])
  have hR := GlobalTheory.ThK.EvUniqInf.rest_pure f M.vac (fun v => (hM.vac v).1) hM.std
  have hR₁ := GlobalTheory.ThK.EvUniqInf.rest_pure (ei f) M₁.vac (fun v => (hM₁.vac v).1) hM₁.std
  have hvac : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hv v).1
  have h1 := he.Heisenberg₂ z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) hR.2
  have e1 : M.co.rho B.ψ z' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ M.vac := hA _ hR
  have e2 : M₁.co.rho B.ψ z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) M₁.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ M₁.vac := hA₁ _ hR₁
  rw [← hz', e1, hl f₁ M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl),
    hl f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl), hvac, e2] at h1
  exact eq_of_pure_eq (fun v => (hM₁.vac v).2.1) hM₁.std h1

end GlobalTheory.ThK.EvCompNe

open GlobalTheory.ThK.EvCompNe in

theorem GlobalTheory.ThK.EvCompNe.comp_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (Mm : Model σ G₁.V' G.W), Mm.IsGood B.ψ →
    ∀ e₁, IsEv B G.M' Mm H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
    ∀ e₂, IsEv B Mm G₁.M' 1 H'.ι (iso0 b H') e₂ →
      ∃ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e₂ (e₁ Φ) ≠ 0 := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ X om om' om₁ om₁' hT hT₁ Mm hMm e₁ he₁ e₂ he₂
  have hB := hT.base
  have hG' := hT.geo.hM'
  have hG₁' := hT₁.geo.hM'
  obtain ⟨ei₁, ev₁, hne₁, hv₁, hl₁⟩ := he₁.loc
  obtain ⟨ei₂, ev₂, hne₂, hv₂, hl₂⟩ := he₂.loc
  have key : ∃ f, ei₂ (ei₁ f) ≠ 0 := by
    by_contra! hall
    obtain ⟨f₀, hf₀⟩ : ∃ f, ei₁ f ≠ 0 := by
      by_contra! h
      exact hne₁ (ContinuousLinearMap.ext h)
    obtain ⟨h, hh⟩ : ∃ h, ei₂ h ≠ 0 := by
      by_contra! h'
      exact hne₂ (ContinuousLinearMap.ext h')
    obtain ⟨y, hy⟩ : ∃ y, ei₂ h y ≠ 0 := by
      by_contra! h'
      exact hh (SchwartzMap.ext h')
    let T : SInf F (Fin b × Fin (a + (b + 2))) →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ).comp ei₂)
    have hTap : ∀ g, T g = ei₂ g y := fun g => rfl
    have hT0 : T = 0 := GlobalTheory.T.schrodinger_invariant_functional_zero (GlobalTheory.ArchUniq.trP F _) (GlobalTheory.ArchUniq.Coord.isPairing_trP _) T (ei₁ f₀) hf₀
      (fun w g₁ hg₁ => by
        obtain ⟨f₁, hf₁⟩ := range_stable hB hG' hMm he₁ ei₁ ev₁ hv₁ hl₁ f₀ w g₁ hg₁
        rw [hTap, ← hf₁, hall f₁]
        rfl)
    exact hy (by rw [← hTap, hT0]; rfl)
  obtain ⟨f, hf⟩ := key
  have hR := GlobalTheory.ThK.EvUniqInf.rest_pure f G.M'.vac (fun v => (hG'.vac v).1) hG'.std
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f G.M'.vac, hR.2, ?_⟩
  have hvac₁ : (fun v => ev₁ v (G.M'.vac v)) = Mm.vac := funext fun v => (hv₁ v).1
  have hvac₂ : (fun v => ev₂ v (Mm.vac v)) = G₁.M'.vac := funext fun v => (hv₂ v).1
  rw [hl₁ f G.M'.vac (fun v => (hG'.vac v).1) (Eventually.of_forall fun _ => rfl), hvac₁,
    hl₂ (ei₁ f) Mm.vac (fun v => (hMm.vac v).1) (Eventually.of_forall fun _ => rfl), hvac₂]
  exact GlobalTheory.ThK.EvNeZero.pure_ne_zero _ hf G₁.M'.vac (fun v => (hG₁'.vac v).2.1) hG₁'.std
