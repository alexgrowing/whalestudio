import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartProduct
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ConeInfCont

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.Published.Metaplectic

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_archOp {X : Type} [TopologicalSpace X] {f : X → SInf F κ} (hf : Continuous f)
    {w : X → (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)} (hw : Continuous w) :
    Continuous fun x => archOp (w x) (f x) := by
  have hp : ∀ y, Continuous fun x => archOp (w x) (f x) y := fun y => by
    have e : ∀ x, archOp (w x) (f x) y = eChar ((-trL (w x).2) y +
        -(Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F)) * ((w x).1 ⬝ᵥ (w x).2)))) * f x (y + (w x).1) :=
      fun x => archS_apply (f x) (w x).2 (w x).1 _ y
    simp only [e, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
    have ht := (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional
    have h := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous.comp hf
    have he : Continuous fun x => f x (y + (w x).1) := h.eval (continuous_const.add hw.fst)
    refine Continuous.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp ?_)).mul
      continuous_const)) he
    exact (ht.comp (continuous_const.dotProduct hw.snd)).neg.add
      (ht.comp (continuous_const.mul (hw.fst.dotProduct hw.snd))).neg
  refine continuous_iff_continuousAt.2 fun x₀ => GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded _ x₀
    (fun y => (hp y).continuousAt) fun a n => ?_
  obtain ⟨q, M, hq, hb⟩ := (tame_archOp (F := F) (κ := κ)).growth (SchwartzMap.seminorm ℂ a n)
    ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a, n))
  have hc : Continuous fun x => (1 + ‖w x‖) ^ M * q (f x) := ((continuous_const.add hw.norm).pow M).mul (hq.comp hf)
  refine ⟨(1 + ‖w x₀‖) ^ M * q (f x₀) + 1, (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).mono fun x hx v => ?_⟩
  exact ((SchwartzMap.le_seminorm ℂ a n _ v).trans (hb _ _)).trans hx.le

theorem continuous_qA : Continuous (qA (F := F)) := by
  have h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)
  exact h.comp continuous_fst

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem locOpInf_rho_eq {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (hM : M.IsGood ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F u)) f = archOp (archW (M.co.e (partInf F u))) f := by
  have h1 : M.co.rho ψ (partInf F u) (pure f M.vac) = pure (locOpInf (M.co.rho ψ (partInf F u)) f) M.vac :=
    (locOpInf_rho M.co hψ u f).1 _ ⟨fun x z hz => finPart_add _ x z hz,
      GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hM.vac v).1) hM.std⟩
  refine eq_of_pure_eq _ (fun v => (hM.vac v).2.1) hM.std _ _ ?_
  rw [← h1]
  have h2 := schr_pureA ψ hψ (M.co.e (partInf F u)) f fun y => ∏ᶠ v, M.vac v fun i => evalV F v (y i)
  have h3 : M.co.e (partInf F u) = mk (realAd F 1).1 0 • M.co.e u := map_smul M.co.e _ _
  rw [show finOp ψ _ (M.co.e (partInf F u)) = _ from h3 ▸ finOp_arch ψ _ _ _] at h2
  exact h2

end SlopeTestRemainingChoices

theorem continuous_coneInfInt : ∀ (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hCfg : CfgA B G G₁ H H') (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F)))
    (hμK : IsNormK K (evI F) μK) (hμ : μ.IsHaarMeasure)
    (l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ) (hl : l ≠ 0)
    (hinv : ∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
    Continuous fun p : KAt K (evI F) × idelesAt E (evI F) => coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f p.1.1 p.2.1 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' _ hT _ e _ ei ev _ _ _ K _ μK μ _ _ l _ _ f
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hM := hT.geo.hM
  have hψ := hT.base.std
  have hΦ : Continuous fun k : KAt K (evI F) => locOpInf (om (k.1, 1)) f :=
    (GlobalTheory.ArchWeilCont.continuousOn_locOpInf hKP.base G.M hT.base.cm hψ hT.weil f).comp_continuous continuous_subtype_val
      fun k => (mem_KAt.1 k.2).2
  generalize (b + 2 - a') / 2 = z
  have hl : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => q.2.1 := continuous_subtype_val.comp continuous_snd
  have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  simp only [coneInfInt, locOpInf_rho_eq hψ hM]
  refine (((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul (ei.continuous.comp (continuous_archOp (hΦ.comp continuous_fst) ?_))
  let L := G.M.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _
    (Matrix.vecMulVec (incV F H.x) (incV F H'.y))).restrictScalars (AF F)))
  have hL : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => G.M.co.e (partInf F (shiftA H H' q.2.1)) :=
    (IsModuleTopology.continuous_of_linearMap L).comp (Units.continuous_val.comp hl)
  exact (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
    (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.snd))

end GlobalTheory.ConeInfCont

end
