import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneLiftStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.SiegelAvgAdm

theorem rho_diagCols' {a b : ℕ} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)}
    (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (AE F E)) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem avgForm_mem_adm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
        GlobalTheory.SiegelAvg.avgForm μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd
    dd₁ hdd₁ ed hmap hheis hinv hadm hnz l₁ hl₁ hl₁inv μ hμ
  have hψ : IsStd B.ψ := hP.base.std
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mA : MeasurableSpace ((Fin n × Fin d₁) → AF F) := borel _
  haveI : BorelSpace ((Fin n × Fin d₁) → AF F) := ⟨rfl⟩
  have hl₁' : ∀ (x y : Fin n × Fin d₁ → AF F), ∀ φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)),
      l₁ (schr B.ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l₁ φ := by
    intro x y φ hφ
    have := hl₁inv (d₁'.e.symm (x, y)) φ hφ
    rwa [rho_diagCols' hdd₁, LinearEquiv.apply_symm_apply] at this
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral F B.ψ hψ _ l₁ hl₁ hl₁' (Measure.addHaar) inferInstance
  intro g hg
  obtain ⟨T, hT⟩ := GlobalTheory.T.pair_adapted_plane_lift hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁'
    dd hdd dd₁ hdd₁ ed hmap hheis hinv hadm hnz Measure.addHaar inferInstance μ hμ g hg
  refine ⟨c₁ • T, fun f => ?_⟩
  obtain ⟨hi, he⟩ := hT f
  have hΦ : pureA F (⇑f) g ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hpt : ∀ y, (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)) =
      c₁ * GlobalTheory.DiagSiegel.diagInt Measure.addHaar (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g))) := fun y => by
    rw [LinearMap.comp_apply]
    exact hc₁ _ (hmap _ (GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hψ _
      (dd.e (Matrix.vecMulVec (incV F H'.y) (Sum.elim y y))) _ hΦ))
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  have hconv : GlobalTheory.SiegelAvg.Conv μ (l₁ ∘ₗ ed) (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y)) (pureA F f g) := by
    show Integrable _ μ
    simp_rw [hpt]
    exact hi.const_mul c₁
  rw [GlobalTheory.SiegelAvg.avgForm_apply _ _ _ hconv]
  simp_rw [hpt]
  rw [integral_const_mul, he]
  rfl

end GlobalTheory.SiegelAvgAdm
end
