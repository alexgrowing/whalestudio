import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThK.InfComp

theorem locOpInf_comp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ k ∈ UAt σ G.V (evI F), ∀ g ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      locOpInf (om (k, 1)) (locOpInf (om (g, 1)) f) = locOpInf (om (k * g, 1)) f := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' _ e _ ei ev _ X om om' om₁ om₁' hT _ k hk g hg f
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hex : ∀ x ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (x, 1)) f f₁ :=
    fun x hx f => GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (b + 2 + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
      hT.base.cm hT.base.std hT.weil x hx f
  exact (GlobalTheory.ThK.InfB.locOpInf_mul hex (fun x Φ hΦ => hS.pres x Φ hΦ) hk hg f).symm

end GlobalTheory.ThK.InfComp

end
