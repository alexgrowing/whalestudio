import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingDarbouxPairSetting
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_darboux_pair_setting : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ := by
  first | exact @GlobalTheory.DblWeilCoord.exists_weil | exact GlobalTheory.DblWeilCoord.exists_weil | (intros; apply GlobalTheory.DblWeilCoord.exists_weil <;> assumption)
