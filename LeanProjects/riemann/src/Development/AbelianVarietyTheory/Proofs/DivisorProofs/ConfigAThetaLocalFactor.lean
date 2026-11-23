import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigFirstMatchedRepsCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftVanishingStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IndLine

theorem twPart_lowPart_irreducible : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      FiniteDimensional ℂ (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)) ∧ KStabL B G.M om R.p G₁.W H' (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)) ∧
      ∀ N : Submodule ℂ R.Pi, N ≤ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) → KStabL B G.M om R.p G₁.W H' N → N = ⊥ ∨ N = twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  haveI := GlobalTheory.T.config_first_matched_reps_compat hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  exact ⟨Submodule.finiteDimensional_of_le (twPart_le B G.M om R.p G₁.W H' X.α _ _),
    GlobalTheory.T.kStabL_twPart_lowPartInf_of_isMatched hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁,
    GlobalTheory.T.config_a_theta_lift_vanishing hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁⟩

end GlobalTheory.IndLine
