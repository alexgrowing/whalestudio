import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotScalar

theorem sub_smul_mem_of_equiv_subQuot :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) →
        ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T he g c hσ s hs
  obtain ⟨e⟩ := he
  have hinj : Function.Injective e.toIntertwiningMap.toLinearMap := e.left_inv.injective
  have key : e.toIntertwiningMap.toLinearMap
        (GlobalTheory.SmGL.subQuot S T g (Submodule.Quotient.mk ⟨s, hs⟩)) =
      e.toIntertwiningMap.toLinearMap (c • Submodule.Quotient.mk ⟨s, hs⟩) := by
    rw [map_smul, ← hσ]
    exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) _
  have h2 := hinj key
  have h3 : (Submodule.Quotient.mk ⟨ρ g s, S.2 g hs⟩ :
        ↥S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) =
      Submodule.Quotient.mk (c • (⟨s, hs⟩ : ↥S.toSubmodule)) := h2
  rw [Submodule.Quotient.eq] at h3
  exact h3

end GlobalTheory.CompanionTheory.SubQuotScalar
