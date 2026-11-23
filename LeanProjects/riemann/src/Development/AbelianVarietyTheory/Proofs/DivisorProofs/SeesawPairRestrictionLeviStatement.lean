import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionLevi
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_pair_restriction_levi : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ t m, IsLevi (W₁ := W₁) H' t 1 m →
        ∀ k : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = k • e Φ) → (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
        (∀ (g : UA σ W.J) (gd : UG (cA σ) (dbl (incM F W.J))),
          (gd.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat g) 0 0 1 →
          ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
        ∀ p : UG (cA σ) (dbl (incM F W.J)),
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat m) 0 0 1 * GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) ((↑t⁻¹ : AE F E) - 1) →
        ∃ Λ : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ, Λ ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
          (∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            Λ (dd.rho B.ψ (z * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) φ) = Λ φ) ∧
          (∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
            Λ (omd p φ) = (k * (((absE F E t : ℝ) ^ (-(n : ℝ)) : ℝ) : ℂ)) * Λ φ) ∧
          ∃ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), Λ φ ≠ 0 := by
  first | exact @GlobalTheory.TorusLamP.exists_lam | exact GlobalTheory.TorusLamP.exists_lam | (intros; apply GlobalTheory.TorusLamP.exists_lam <;> assumption)
