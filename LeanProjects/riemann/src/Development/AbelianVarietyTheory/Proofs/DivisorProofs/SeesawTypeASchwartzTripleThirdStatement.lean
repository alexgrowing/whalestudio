import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeASchwartzTripleThird
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_a_schwartz_triple_third : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F), ∀ S : Set (SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsCompact S → ∀ N : ℕ, ∃ C : ℝ,
      ∀ f ∈ S, ∀ t : AE F E, (pairA F 1 0 : AF F) • t = t → ∀ y : Fin b × Fin (b + a') → AF F,
        ‖e (G.M.co.rho B.ψ (t • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (pureA F f g)) y‖ ≤
          C * ((1 + GlobalTheory.IdeleDecay.size F E t) ^ N)⁻¹ := by
  first | exact @GlobalTheory.ConeArchDecay.norm_ev_shift_arch_le | exact GlobalTheory.ConeArchDecay.norm_ev_shift_arch_le | (intros; apply GlobalTheory.ConeArchDecay.norm_ev_shift_arch_le <;> assumption)
