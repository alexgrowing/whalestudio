import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorCharacter
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
theorem _root_.GlobalTheory.T.archimedean_polynomial_tensor_character : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (A : InfinitePlace F → Matrix (Fin n) (Formalism.BasicNotions.TH.Ix P Q) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℚ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w)) →
    (∀ w, X.θ w * A w = A w * Formalism.BasicNotions.TH.Jm P Q) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (Formalism.BasicNotions.TH.fockAct1 P Q R S) (fun w => -((c w : ℚ) : ℂ)) →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ T, IsKFix B om (Φ T) ↔ T ∈ GlobalTheory.KFixIrr.chiPart (InfinitePlace F) P Q R S c := by
  first | exact @GlobalTheory.KFixIrr.kFix_iff_mem_chiPart | exact GlobalTheory.KFixIrr.kFix_iff_mem_chiPart | (intros; apply GlobalTheory.KFixIrr.kFix_iff_mem_chiPart <;> assumption)
