import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxModelCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
      IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
    ∃ D : Matrix (Fin d) (Fin n ⊕ Fin n) E →ₗ[F]
        ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F),
      Function.Injective D ∧ ∀ u, dd.e (incM F u) = GlobalTheory.SiegelConv.ratP (D u) := by
  first | exact @GlobalTheory.SiegelConvRat.ratCoord | exact GlobalTheory.SiegelConvRat.ratCoord | (intros; apply GlobalTheory.SiegelConvRat.ratCoord <;> assumption)
