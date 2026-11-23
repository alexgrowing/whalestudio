import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartProduct

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeInfMeasB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.ConeArchB GlobalTheory.XTermDecay in

theorem continuous_coneInfInt (hP : GlobalTheory.FunPr.Hypotheses₂) (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)}
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)) {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
    (K : Subgroup (UA σ G.V'.J)) (z : ℕ) (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) :
    Continuous fun q : KAt K (evI F) × idelesAt E (evI F) =>
      coneInfInt B G.M' om' ei (shiftB σ H H') X.ν z f q.1.1 q.2.1 := by
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hM := hT.geo.hM'
  have hψ := hT.base.std
  have hΦc : Continuous fun k : KAt K (evI F) => locOpInf (om' (k.1, 1)) f :=
    (GlobalTheory.ArchWeilCont.continuousOn_locOpInf hP G.M' hT.base.cm hψ hT.weil' f).comp_continuous
      continuous_subtype_val fun k => k.2.2
  have hl : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => q.2.1 := continuous_subtype_val.comp continuous_snd
  have hν : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  simp only [coneInfInt, (locOpInf_rho_eq hψ hM _ _).2]
  refine (((continuous_subtype_val.comp hν).comp hl).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (GlobalTheory.Doubling.continuous_absE.comp hl))).pow z)).smul
    (ei.continuous.comp (continuous_archOp (hΦc.comp continuous_fst) ?_))
  let L := G.M'.co.e.toLinearMap ∘ₗ (realAd F 1 • ((LinearMap.toSpanSingleton (AE F E) _
    (Matrix.vecMulVec (incV F H.y) (incV F H'.x))).restrictScalars (AF F) ∘ₗ (cA σ).toLinearMap))
  have hL : Continuous fun q : KAt K (evI F) × idelesAt E (evI F) => G.M'.co.e (partInf F (shiftB σ H H' q.2.1)) :=
    (IsModuleTopology.continuous_of_linearMap L).comp (Units.continuous_val.comp hl)
  exact (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.fst)).prodMk
    (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp hL.snd))

theorem aestronglyMeasurable_coneInfInt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (_hKP : KP) (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)}, CfgB B G G₁ H H' →
    ∀ {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W},
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)}, IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei' ≠ 0 → (∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
      (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v)) →
    (∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v)) →
    ∀ {K : Subgroup (UA σ G.V'.J)}, IsStab B K →
    ∀ (μKI : Measure (KAt K (evI F))) (μI : Measure (idelesAt E (evI F))), IsNormK K (evI F) μKI → μI.IsHaarMeasure →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (y : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F),
      AEStronglyMeasurable (fun p : KAt K (evI F) × idelesAt E (evI F) => coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f p.1.1 p.2.1 y) (μKI.prod μI) ∧
      ∀ k ∈ KAt K (evI F), AEStronglyMeasurable (fun l : idelesAt E (evI F) => coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f k l.1 y) μI := by
  intro F E _ _ _ _ _ σ hKP B a b G G₁ H H' _ X om om' om₁ om₁' hT _ e' _ ei' ev' _ _ _ K _ μKI μI _ _ f y
  classical
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hc := ((BoundedContinuousFunction.evalCLM ℂ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).continuous.comp
    (continuous_coneInfInt hKP.base B H H' hT ei' K ((a - (b + 2)) / 2 + 1) f)
  exact ⟨hc.aestronglyMeasurable, fun k hk =>
    (hc.comp ((continuous_const (y := (⟨k, hk⟩ : KAt K (evI F)))).prodMk continuous_id)).aestronglyMeasurable⟩

end GlobalTheory.ConeInfMeasB

end
