import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartTriple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_B_local_part_triple : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (idelesAt E (evI F)), μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (h : idelesAt E (evI F) → ℝ), Integrable h μ ∧
      (∀ φ : SInf F (Fin (b + 2) × Fin (a + (b + 2))), AEStronglyMeasurable (fun y : idelesAt E (evI F) =>
        l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) φ))) μ) ∧
      ∀ (φ : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (y : idelesAt E (evI F)),
        ‖l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) φ))‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F) ℂ)) φ * h y := by
  first | exact @GlobalTheory.ConeBoundB.cone_integrand_bound | exact GlobalTheory.ConeBoundB.cone_integrand_bound | (intros; apply GlobalTheory.ConeBoundB.cone_integrand_bound <;> assumption)
