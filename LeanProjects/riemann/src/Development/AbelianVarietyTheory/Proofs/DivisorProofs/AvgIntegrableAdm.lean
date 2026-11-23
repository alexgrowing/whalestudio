import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedModelTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSpanFinrankStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelX

theorem avg_integrable_adm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l ∘ₗ ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ≠ 0) →
      ∀ l₁ : ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ, l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d) →
        (∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l₁ (dd₁.rho B.ψ (z * (diagCols (Fin d))ᵀ) φ) = l₁ φ) →
      ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Integrable (GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ) μ) ∧
        GlobalTheory.DblSiegelX.avgL dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) μ ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he hne dd dd₁ hdd hdd₁
    ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ
  obtain ⟨Λ, hiso, hrk, hinvΛ, b, w, hw, hnd, hcoord⟩ := GlobalTheory.T.pair_adapted_model_transfer F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁
    r₁ s₁ hH hP₁ dd dd₁ hdd hdd₁ ed hmap hheis hinv l₁ hl₁inv
  obtain ⟨ν, hν, htr⟩ := GlobalTheory.T.adelic_haar_coordinates F E (Fin 2) b d μ hμ
  obtain ⟨hI, l', hl', hl'eq⟩ := GlobalTheory.T.lagrangian_span_finrank F B.ψ hP.base.std _ Λ hiso hrk (Fin d × Fin 2) w hw hnd (l₁ ∘ₗ ed) (hadm l₁ hl₁)
    hinvΛ ν hν
  have hfun : ∀ Φ, GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ = fun u =>
      (fun t : Fin d × Fin 2 → AF F => (l₁ ∘ₗ ed) (schr B.ψ (∑ p, t p •
        ((fun k => algebraMap F (AF F) ((w p).1 k)), (fun k => algebraMap F (AF F) ((w p).2 k)))) Φ))
        (fun p => (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2) := by
    intro Φ; funext u
    simp only [GlobalTheory.DblSiegelX.avgFun, Darboux.rho]
    rw [hcoord u]
  have hint : ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      Integrable (GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ) μ := by
    intro Φ hΦ; rw [hfun]; exact (htr _).1 (hI Φ hΦ)
  refine ⟨hint, ?_⟩
  intro g hg
  obtain ⟨T, hT⟩ := hl' g hg
  refine ⟨T, fun f => ?_⟩
  have hmem : pureA F (⇑f) g ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  rw [GlobalTheory.DblSiegelX.avgL_apply _ _ _ _ _ _ (hint _ hmem), hfun, (htr _).2, ← hl'eq _ hmem, hT]

end GlobalTheory.DblSiegelX

end
