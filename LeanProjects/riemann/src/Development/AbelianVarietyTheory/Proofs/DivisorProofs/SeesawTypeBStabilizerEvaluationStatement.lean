import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBStabilizerEvaluation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical nonZeroDivisors
open GlobalTheory.Doubling (absE)
open GlobalTheory.LocIdeal (locId)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_b_stabilizer_evaluation : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
    ∀ y : Fin b × Fin (a + b) → AF F, ∃ (g : (AE F E)ˣ → ℝ) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 ∧ Measurable g ∧
      (∀ l, ∀ m ∈ idelesAt E (fun x : AF F => x.2), g (l * m) = g l) ∧
      (∀ μi : Measure (idelesAt E (evI F)), μi.IsHaarMeasure →
        Integrable (fun m : idelesAt E (evI F) => g m.1 * (absE F E m.1 : ℝ) ^ ((a - (b + 2)) / 2 + 1)) μi) ∧
      ∀ (k : K) (l : (AE F E)ˣ), ‖coneInt B G.M' om' e' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) k.1 l y‖ ≤
        g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
          (absE F E l : ℝ) ^ ((a - (b + 2)) / 2 + 1) := by
  first | exact @GlobalTheory.ConeMajorant.coneInt_pure_le | exact GlobalTheory.ConeMajorant.coneInt_pure_le | (intros; apply GlobalTheory.ConeMajorant.coneInt_pure_le <;> assumption)
