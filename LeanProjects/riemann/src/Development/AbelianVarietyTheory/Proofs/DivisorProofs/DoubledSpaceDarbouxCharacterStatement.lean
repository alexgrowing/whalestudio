import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceDarbouxCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_space_darboux_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (χ : Chr F E) (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
      (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
      IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      SiegelRule (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χ (diagCols (Fin d)) omd →
      ∀ l ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d),
        (∀ (y₁ y₂ : Fin n → AE F E) (Z : Matrix (Fin n) (Fin d₁) (AE F E)), ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          l (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y₁ (incV F H'.x) + Z * (incM F H'.ι)ᵀ)
            (Matrix.vecMulVec y₂ (incV F H'.x) + Z * (incM F H'.ι)ᵀ)) Ψ) = l Ψ) →
        ∀ (t : (AE F E)ˣ) (p : UG (cA σ) (dbl (incM F W.J))),
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = t.1 • Sum.elim (incV F H'.x) (0 : Fin d → AE F E) →
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) →
          (p.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromRows (incM F H'.ι) (incM F H'.ι) =
            Matrix.fromRows (incM F H'.ι) (incM F H'.ι) →
          ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), l (omd p Ψ) = (χ t : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * l Ψ := by
  first | exact @GlobalTheory.DiagLagrMove.siegelRule_plane | exact GlobalTheory.DiagLagrMove.siegelRule_plane | (intros; apply GlobalTheory.DiagLagrMove.siegelRule_plane <;> assumption)
