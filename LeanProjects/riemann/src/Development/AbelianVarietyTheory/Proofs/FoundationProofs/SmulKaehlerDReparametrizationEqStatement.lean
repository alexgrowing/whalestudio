import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open GlobalTheory.K5 GlobalTheory.Glue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_kaehlerD_reparametrization_eq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  first | exact @GlobalTheory.Glue.DPsi.smul_D_psi | exact GlobalTheory.Glue.DPsi.smul_D_psi | (intros; apply GlobalTheory.Glue.DPsi.smul_D_psi <;> assumption)
