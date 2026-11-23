import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneCompatibleStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelAvgNz

theorem avg_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0) →
      ∀ l₁ : (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ) →ₗ[ℂ] ℂ, l₁ ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin d₁) (Fin n) (AE F E)), ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)),
          l₁ (dd₁.rho B.ψ (z * (diagCols (Fin n))ᵀ) φ) = l₁ φ) →
        (∃ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l₁ φ ≠ 0) →
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
        ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), GlobalTheory.SiegelAvg.avgForm μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) Φ ≠ 0 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv hl₁0 μ hμ
  obtain ⟨φ₀, hφ₀, hl0⟩ := hl₁0
  obtain ⟨Tm, hTm, hTh, hTi, hTa, hTv⟩ := GlobalTheory.T.pair_adapted_plane_compatible hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁
    r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ μ hμ
  obtain ⟨c, hc⟩ := GlobalTheory.T.seesaw_pair_restriction_global_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁'
    dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz Tm hTm hTh hTi hTa
  obtain ⟨Φ, hΦ, g, ⟨hgi, hg0⟩, hgv⟩ := hTv φ₀ hφ₀
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  have hψ : IsStd B.ψ := hP.base.std
  have hmem : ∀ y, GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := fun y =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hψ _ _ Φ hΦ
  have hφne : φ₀ ≠ 0 := by rintro rfl; exact hl0 (map_zero l₁)
  obtain ⟨y₀, hy₀⟩ : ∃ y, g y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg0
    rw [show g = fun _ => 0 from funext h]
    exact integral_zero _ _
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := hc _ (hmem y₀)
    rw [hgv, zero_smul] at this
    exact smul_ne_zero hy₀ hφne this
  have key : ∀ y, (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ) = (c⁻¹ * l₁ φ₀) * g y := fun y => by
    have h1 := hc _ (hmem y)
    rw [hgv] at h1
    have h2 : ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ) = (c⁻¹ * g y) • φ₀ := by
      rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [LinearMap.comp_apply, h2, map_smul, smul_eq_mul]
    ring
  have hconv : GlobalTheory.SiegelAvg.Conv μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) Φ := by
    show Integrable (fun y => (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ)) μ
    simp_rw [key]
    exact hgi.const_mul _
  refine ⟨Φ, hΦ, ?_⟩
  rw [GlobalTheory.SiegelAvg.avgForm_apply _ _ _ hconv]
  simp_rw [key]
  rw [integral_const_mul]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hc0) hl0) hg0

end GlobalTheory.SiegelAvgNz
end
