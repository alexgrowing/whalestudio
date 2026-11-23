import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedThetaLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Formalism.LocalRingCardinality.DataTheta
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_B_matched_theta_local : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (act : InfinitePlace F → Formalism.BasicNotions.TH.Mat Rn Sn →ₗ[ℂ] Module.End ℂ R.Pi)
        (c c' : InfinitePlace F → ℂ),
        (∀ w X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X) ∧
        (∀ w w', w ≠ w' → ∀ X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w X * act w' Y = act w' Y * act w X) ∧
        (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ lowPartInf B G.M R.p, act w X v ∈ lowPartInf B G.M R.p) ∧
        (∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ N, act w X v ∈ N) →
          N = ⊥ ∨ N = lowPartInf B G.M R.p) ∧
        (∀ v, v ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) ↔ v ∈ lowPartInf B G.M R.p ∧
          ∀ w, act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧ act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) ∧
        (∀ v ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
          ∀ j, j ≠ s₀ → act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) ∧
        ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → KStabL B G.M om R.p G₁.W H' N →
          ∀ w X, Formalism.BasicNotions.TH.IsKC X → (∀ a, X a (.inl r₀) = 0 ∧ X (.inl r₀) a = 0 ∧ X a (.inr s₀) = 0 ∧ X (.inr s₀) a = 0) →
            ∀ v ∈ N, act w X v ∈ N := by
  first | exact @GlobalTheory.FockBottom.bridge_beta | exact GlobalTheory.FockBottom.bridge_beta | (intros; apply GlobalTheory.FockBottom.bridge_beta <;> assumption)
