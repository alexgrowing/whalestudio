import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalAntiInvolutionGelfandTrick
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_anti_involution_gelfand_trick : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∃ θ : GlobalTheory.SphLine.locU σ G.W v → GlobalTheory.SphLine.locU σ G.W v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ (GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v),
        ∃ b ∈ (GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v), θ g = a * g * b := by
  first | exact @GlobalTheory.SphLine.gelfand_inv | exact GlobalTheory.SphLine.gelfand_inv | (intros; apply GlobalTheory.SphLine.gelfand_inv <;> assumption)
