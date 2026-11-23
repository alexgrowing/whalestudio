import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaLiftRecursion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_theta_lift_recursion : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ ι : R.Pi →ₗ[ℂ] R₁.Pi, (∀ y ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p), ι y = 0 → y = 0) ∧
        (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)).map ι = lowPartInf B G₁.M R₁.p ∧
        KStabL B G.M om R.p G₁.W H' (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) ∧
        ∀ k ∈ KInf σ G.W B.emb, ∀ k₁ ∈ KInf σ G₁.W B.emb, IsLevi H' 1 k₁ k →
          ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) f f₁ →
          R.p f ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) → ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin a × Fin (a + b)),
          Acts (evI F) (om₁ (1, k₁)) g g₁ → ι (R.p f) = R₁.p g → ι (R.p f₁) = R₁.p g₁ := by
  first | exact @GlobalTheory.BranchIsoB.twPart_iso_lowPart | exact GlobalTheory.BranchIsoB.twPart_iso_lowPart | (intros; apply GlobalTheory.BranchIsoB.twPart_iso_lowPart <;> assumption)
