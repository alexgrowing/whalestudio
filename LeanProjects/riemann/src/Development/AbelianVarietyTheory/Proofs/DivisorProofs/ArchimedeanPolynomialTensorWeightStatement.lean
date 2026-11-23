import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_polynomial_tensor_weight : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℂ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (Formalism.BasicNotions.TH.fockAct2 P Q R S) c →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ N : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S),
      (∀ k ∈ KInf σ W B.emb, ∀ T ∈ N, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (Φ T) f₁ → f₁ ∈ N.map Φ) →
      ∀ w (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z → ∀ T ∈ N,
        GlobalTheory.RealLift.atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T ∈ N := by
  first | exact @GlobalTheory.FockKStab.kstab | exact GlobalTheory.FockKStab.kstab | (intros; apply GlobalTheory.FockKStab.kstab <;> assumption)
