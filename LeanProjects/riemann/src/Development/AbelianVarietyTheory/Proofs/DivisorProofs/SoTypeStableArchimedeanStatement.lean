import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoTypeStableArchimedean
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.so_type_stable_archimedean : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F), ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
      om' (g', h) Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  first | exact @GlobalTheory.ThK.so_stable_arch | exact GlobalTheory.ThK.so_stable_arch | (intros; apply GlobalTheory.ThK.so_stable_arch <;> assumption)
