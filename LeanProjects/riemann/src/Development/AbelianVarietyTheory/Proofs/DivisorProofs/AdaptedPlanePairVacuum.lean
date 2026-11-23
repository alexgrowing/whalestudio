import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleVectorHaarExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFunctionalContinuousStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.DblSiegelNZ

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ a (schr ψ b φ) = ψ (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) • schr ψ b (schr ψ a φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, add_dotProduct]
  rw [show x + a.1 + b.1 = x + b.1 + a.1 by abel]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem schr_zero {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def zsL {n n₁ d : ℕ} (H : Plane E n n₁) : (Fin d → AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) where
  toFun := GlobalTheory.DblSiegelX.zs H
  map_add' u v := by
    ext i j
    simp [GlobalTheory.DblSiegelX.zs, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' a u := by
    ext i j
    simp [GlobalTheory.DblSiegelX.zs, Matrix.vecMulVec, Matrix.mulVec, dotProduct]
    rw [← Finset.smul_sum, mul_smul_comm]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∃ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ l₁ : ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ, l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d) ∧
        (∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l₁ (dd₁.rho B.ψ (z * (diagCols (Fin d))ᵀ) φ) = l₁ φ) ∧
        ∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ∫ u, GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ u ∂μ ≠ 0 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he he0 dd dd₁ hdd hdd₁
    ed hmaps hheis hinv hadm hne
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨Φ₀, hΦ₀, hedΦ₀⟩ := hne
  obtain ⟨l₁, hl₁, hl₁inv, w, hw⟩ := GlobalTheory.DiagNonvan.exists_invForm_rho_ne_zero F E σ (Fin n₁) (Fin d) (Fin n₁ × Fin d) B.ψ
    (incM F X₁.J) (incM F W.J) M₁.co dd₁ hψ hdd₁ (ed Φ₀) (hmaps Φ₀ hΦ₀) hedΦ₀
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.adele_vector_haar_exists F E d
  refine ⟨μ, hμ, l₁, hl₁, hl₁inv, ?_⟩
  have hmem : ∀ (v : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      dd.rho B.ψ v Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := fun v Φ hΦ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ hΦ
  set Φ₁ := dd.rho B.ψ (incM F H.ι * w) Φ₀ with hΦ₁def
  have hΦ₁ : Φ₁ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := hmem _ Φ₀ hΦ₀
  have hl₁Φ₁ : l₁ (ed Φ₁) ≠ 0 := by rw [hΦ₁def, hheis w Φ₀ hΦ₀]; exact hw
  obtain ⟨p, hpadd, hp, hpsep⟩ := GlobalTheory.T.pair_adapted_projection_exists F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH
  by_contra hcon
  push_neg at hcon
  set N := GlobalTheory.DblSiegelX.avgFun dd B.ψ (GlobalTheory.DblSiegelX.zs H) (l₁ ∘ₗ ed) Φ₁ with hNdef
  have hNc : Continuous N :=
    GlobalTheory.T.schrodinger_functional_continuous F E B.ψ hψ _ (l₁ ∘ₗ ed) (hadm l₁ hl₁) Φ₁ hΦ₁ d (dd.e.toLinearMap ∘ₗ zsL H)
  have hNi : Integrable N μ :=
    (GlobalTheory.T.adapted_plane_pair_restriction_alt hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he he0 dd dd₁ hdd hdd₁
      ed hmaps hheis hinv hadm ⟨Φ₀, hΦ₀, hedΦ₀⟩ l₁ hl₁ hl₁inv μ hμ).1 Φ₁ hΦ₁
  have key : ∀ c, ∫ u, B.ψ (p c u) * N u ∂μ = 0 := by
    intro c
    have h := hcon (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) c) Φ₁) (hmem _ _ hΦ₁)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hNdef, GlobalTheory.DblSiegelX.avgFun, LinearMap.comp_apply, Darboux.rho]
    rw [schr_comm, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul]
    have hi := hinv c (dd.rho B.ψ (GlobalTheory.DblSiegelX.zs H u) Φ₁) (hmem _ _ hΦ₁)
    simp only [Darboux.rho] at hi
    rw [hi, hp c u, dd.form]
  have hN0 := GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ d (Fin d ⊕ Fin d → AE F E) p hpadd hpsep μ hμ N hNc hNi key
  apply hl₁Φ₁
  have h0 := congrFun hN0 0
  have hz : GlobalTheory.DblSiegelX.zs H (0 : Fin d → AE F E) = 0 := (zsL (F := F) H).map_zero
  simp only [hNdef, GlobalTheory.DblSiegelX.avgFun, LinearMap.comp_apply, Darboux.rho, hz, map_zero, schr_zero,
    Pi.zero_apply] at h0
  exact h0

end GlobalTheory.DblSiegelNZ
