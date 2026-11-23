import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.InfB

theorem locOpInf_mul_V' : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ p ∈ UAt σ G.V' (evI F), ∀ g ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin a' × Fin (a + a')),
      locOpInf (om' (p * g, 1)) f = locOpInf (om' (p, 1)) (locOpInf (om' (g, 1)) f) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT p hp g hg f
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om'
    hT.base.cm hT.base.std hT.weil'
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F _ :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  exact GlobalTheory.ThK.InfB.locOpInf_mul hex hpres hp hg f

end GlobalTheory.ThK.InfB
