import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPairDescentModel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_pair_descent_model : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
      ∃ (κa : Type) (_ : Fintype κa) (ε : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ κa ⊕ ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)))
        (C : Matrix κa (Fin n) E)
        (S : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
        (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) ∧
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), S Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d))) ∧
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ∃ l' ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l' Φ = l (S Φ)) ∧
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          (fun v => S (dd.rho B.ψ (incM F H'.ι * z) Φ) (GlobalTheory.ThK.Adapt.glue ε 0 v)) =
            dd₁.rho B.ψ z (fun v => S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v))) ∧
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ∀ v,
          S (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) (GlobalTheory.ThK.Adapt.glue ε 0 v) = S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v)) ∧
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), (fun v => S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v)) ≠ 0) ∧
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ∀ v,
          S (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y Φ) (GlobalTheory.ThK.Adapt.glue ε 0 v) =
            S Φ (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) := by
  first | exact @GlobalTheory.MixedModel.mixed_model | exact GlobalTheory.MixedModel.mixed_model | (intros; apply GlobalTheory.MixedModel.mixed_model <;> assumption)
