import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaIntegralUnfold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeAArchimedeanEvaluation
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ThK.ConeInfDerivMeas

theorem continuous_iteratedFDeriv_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (n : ℕ)
    (y : κ → mixedEmbedding.mixedSpace F) : Continuous fun f : SInf F κ => iteratedFDeriv ℝ n (⇑f) y := by
  refine continuous_iff_continuousAt.2 fun f₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h : Continuous fun f : SInf F κ => SchwartzMap.seminorm ℂ 0 n (f - f₀) :=
    ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (0, n)).comp (continuous_id.sub continuous_const)
  have h' := h.tendsto f₀
  rw [sub_self, map_zero] at h'
  refine squeeze_zero (fun _ => norm_nonneg _) (fun f => ?_) h'
  rw [← iteratedFDeriv_sub_apply ((f.smooth n).contDiffAt) ((f₀.smooth n).contDiffAt)]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (f - f₀) n y

theorem secondCountable_multilinear_forms (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) : SecondCountableTopology (V [×n]→L[ℝ] ℂ) := by
  haveI : FiniteDimensional ℝ (V [×n]→L[ℝ] ℂ) := Module.Finite.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ)) ContinuousMultilinearMap.toMultilinearMap_injective
  haveI := FiniteDimensional.proper_real (V [×n]→L[ℝ] ℂ)
  infer_instance

theorem stronglyMeasurable_iteratedFDeriv_coneInfInt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (z : ℕ) (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (n : ℕ) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
      StronglyMeasurable (Function.uncurry fun (k : KAt K (evI F)) (l : idelesAt E (evI F)) =>
        iteratedFDeriv ℝ n (⇑(coneInfInt B G.M om ei (shiftA H H') X.ν z f k.1 l.1)) y) := by
  intro F E _ _ _ _ _ σ hP B b a' G G₁ H H' X om om' _ hT _ e _ ei ev _ _ _ K _ z f n y
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hM := hT.geo.hM
  have hψ := hT.base.std
  have hΦ : Continuous fun k : KAt K (evI F) => locOpInf (om (k.1, 1)) f :=
    (GlobalTheory.ArchWeilCont.continuousOn_locOpInf hP G.M hT.base.cm hψ hT.weil f).comp_continuous continuous_subtype_val
      fun k => k.2.2
  have hl : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => q.2.1 := continuous_subtype_val.comp continuous_snd
  have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  have hc : Continuous fun p : KAt K (evI F) × idelesAt E (evI F) =>
      coneInfInt B G.M om ei (shiftA H H') X.ν z f p.1.1 p.2.1 := by
    simp only [coneInfInt, GlobalTheory.ConeInfCont.locOpInf_rho_eq hψ hM]
    refine (((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul
        (ei.continuous.comp (GlobalTheory.ConeInfCont.continuous_archOp (hΦ.comp continuous_fst) ?_))
    let L := G.M.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _
      (Matrix.vecMulVec (incV F H.x) (incV F H'.y))).restrictScalars (AF F)))
    have hL : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => G.M.co.e (partInf F (shiftA H H' q.2.1)) :=
      (IsModuleTopology.continuous_of_linearMap L).comp (Units.continuous_val.comp hl)
    exact (continuous_pi fun i => GlobalTheory.ConeInfCont.continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
      (continuous_pi fun i => GlobalTheory.ConeInfCont.continuous_qA.comp ((continuous_apply i).comp hL.snd))
  have hd := (continuous_iteratedFDeriv_apply n y).comp hc
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V.J
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : SecondCountableTopology (KAt K (evI F)) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : BorelSpace (KAt K (evI F)) := Subtype.borelSpace _
  haveI := secondCountable_multilinear_forms (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) n
  exact hd.stronglyMeasurable

end GlobalTheory.ThK.ConeInfDerivMeas

end
