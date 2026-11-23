import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1SplitConfigBIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1SplitConfigBRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1SplitConfigBFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1SplitConfigAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1SplitConfigAIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1SplitConfigARealStatement

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

theorem h1B : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      (∀ v : Pl F, IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2)) ∧
        IndLineInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  refine ⟨fun v => ?_, GlobalTheory.T.indLineInf_beta_half_a_of_isMatched hKP F E σ B a b G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁⟩
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with h | h
  · exact GlobalTheory.T.indLineFin_beta_of_isMatched_of_isEmpty_algHom hKP F E σ B a b G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁ v h
  · exact GlobalTheory.T.indLineFin_beta_half_a_of_isMatched_of_nonempty_algHom hKP F E σ B a b G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁ v h

theorem h1A : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      (∀ v : Pl F, IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2)) ∧
        IndLineInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  refine ⟨fun v => ?_, GlobalTheory.T.indLineInf_alpha_of_isMatched hKP F E σ B b a' G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁⟩
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with h | h
  · exact GlobalTheory.T.indLineFin_alpha_of_isMatched_of_isEmpty_algHom hKP F E σ B b a' G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁ v h
  · exact GlobalTheory.T.indLineFin_alpha_of_isMatched_of_nonempty_algHom hKP F E σ B b a' G G₁ H H' hc X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁ v h

theorem h1 : (GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      (∀ v : Pl F, IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2)) ∧
        IndLineInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2)) ∧
    (GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      (∀ v : Pl F, IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2)) ∧
        IndLineInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2)) :=
  ⟨h1B, h1A⟩

end GlobalTheory.IndLine
