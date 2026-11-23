import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairDescentCaseB
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
theorem _root_.GlobalTheory.T.matched_pair_descent_case_b : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ g₀ ∈ fockDeg G₁.M B.ψ B.emb (lowDegInf B G₁.M R₁.p), ∃ f₀ ∈ G.M.Pol B.ψ B.emb,
        R.p f₀ ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) ∧ R.p f₀ ≠ 0 ∧
        ∀ (ι : Type) (s : Finset ι) (c : ι → ℂ) (k : ι → UA σ G.W.J) (k₁ : ι → UA σ G₁.W.J)
          (g : ι → SInf F (Fin a × Fin (a + b))) (f : ι → SInf F (Fin a × Fin (a + (b + 2)))),
          (∀ i ∈ s, k i ∈ KInf σ G.W B.emb ∧ k₁ i ∈ KInf σ G₁.W B.emb ∧ IsLevi H' 1 (k₁ i) (k i) ∧
            Acts (evI F) (om₁ (1, k₁ i)) g₀ (g i) ∧ Acts (evI F) (om (1, k i)) f₀ (f i)) →
          ∑ i ∈ s, c i • R₁.p (g i) = 0 → ∑ i ∈ s, c i • R.p (f i) = 0 := by
  first | exact @GlobalTheory.FockInclCyc.exists_cyclic_pair | exact GlobalTheory.FockInclCyc.exists_cyclic_pair | (intros; apply GlobalTheory.FockInclCyc.exists_cyclic_pair <;> assumption)
