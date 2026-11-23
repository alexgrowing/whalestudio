import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionAdapted
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
theorem _root_.GlobalTheory.T.seesaw_pair_restriction_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        (∀ x : Matrix (Fin d₁) (Fin n ⊕ Fin n) E, ∃ u v : (Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → F,
          dd₁.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
      ∃ (κa : Type) (_ : Fintype κa) (ε : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ κa ⊕ ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)))
        (C : Matrix κa (Fin n) E)
        (dN : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        (∀ x : Matrix (Fin d) (Fin n ⊕ Fin n) E, ∃ u v : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F,
          dN.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) ∧
        (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) ∧
        (∀ z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E),
          dN.e (incM F H'.ι * z) = (GlobalTheory.ThK.Adapt.glue ε 0 (dd₁.e z).1, GlobalTheory.ThK.Adapt.glue ε 0 (dd₁.e z).2)) ∧
        (∀ y : Fin n ⊕ Fin n → AE F E, ∃ q : κa → AF F,
          dN.e (Matrix.vecMulVec (incV F H'.x) y) = (0, GlobalTheory.ThK.Adapt.glue ε q 0)) ∧
        (∀ y : Fin n → AE F E, dN.e (Matrix.vecMulVec (incV F H'.y) (Sum.elim y y)) =
          (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) 0, 0)) := by
  first | exact @GlobalTheory.MixedCoord.exists_coord | exact GlobalTheory.MixedCoord.exists_coord | (intros; apply GlobalTheory.MixedCoord.exists_coord <;> assumption)
