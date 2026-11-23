import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory.ThK.ArchActs

theorem acts_inf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ k ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin a × Fin (a + a')), ∃ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (k, 1)) f f₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT k hk f
  exact GlobalTheory.ArchLocalityX.acts_arch_left hK.base F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
    hT.base.cm hT.base.std hT.weil k hk f

end GlobalTheory.ThK.ArchActs
