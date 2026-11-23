import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRestrictionCompatiblePair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_restriction_compatible_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n d r s r₁ s₁ : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r₁ s₁ →
    ∀ (χX χW : Chr F E), IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
    ∀ cb co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      cb.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (Mb M₁ : Model σ X W) (omb om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      Mb.co = cb ∧ M₁.co = co ∧ IsPair B Mb χX χW omb r s r₁ s₁ ∧ IsPair B M₁ χX χW om₁ r s r₁ s₁ ∧
      Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d)) ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧ (∀ x, e (omb x Φ) = om₁ x (e Φ)) ∧
        ∀ u, e (cb.rho B.ψ u Φ) = co.rho B.ψ u (e Φ) := by
  first | exact @GlobalTheory.TwoModels.exists_two_models | exact GlobalTheory.TwoModels.exists_two_models | (intros; apply GlobalTheory.TwoModels.exists_two_models <;> assumption)
