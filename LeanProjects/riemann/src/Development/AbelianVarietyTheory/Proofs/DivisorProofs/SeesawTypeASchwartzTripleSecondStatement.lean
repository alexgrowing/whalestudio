import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeASchwartzTripleSecond
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_a_schwartz_triple_second : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F), ∀ m : ℕ, 0 < m →
      ∃ (r : ℕ) (gs : Fin r → (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F) → ℂ),
        (∀ j, gs j ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ l : (AE F E)ˣ, (∀ i v, evFin F v ((m : AF F) * GlobalTheory.IdeleDecay.coord F E l.1 i) ∈ v.adicCompletionIntegers F) →
          ∃ j, ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
            G.M.co.rho B.ψ (shiftA H H' l) (pureA F f g) =
              G.M.co.rho B.ψ (((pairA F 1 0 : AF F) • l.1) • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (pureA F f (gs j)) := by
  first | exact @GlobalTheory.FinFinite.rho_shiftA_pureA_finite | exact GlobalTheory.FinFinite.rho_shiftA_pureA_finite | (intros; apply GlobalTheory.FinFinite.rho_shiftA_pureA_finite <;> assumption)
