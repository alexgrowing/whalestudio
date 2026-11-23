import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBTriplesReconfiguration
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.configuration_b_triples_reconfiguration : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
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
  first | exact @GlobalTheory.ConeInfMeasB.aestronglyMeasurable_coneInfInt | exact GlobalTheory.ConeInfMeasB.aestronglyMeasurable_coneInfInt | (intros; apply GlobalTheory.ConeInfMeasB.aestronglyMeasurable_coneInfInt <;> assumption)
