import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaNonsplitInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_theta_nonsplit_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ k ∈ KAt σ G.W v, ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, k)) φ φ₁ → Rf.p v φ₁ = Rf.p v φ) → ∃ c : ℂ, Rf.p v φ = c • Rf.p v (G.M.vac v) := by
  first | exact @GlobalTheory.SphLine.fixed_eq_smul_vac | exact GlobalTheory.SphLine.fixed_eq_smul_vac | (intros; apply GlobalTheory.SphLine.fixed_eq_smul_vac <;> assumption)
