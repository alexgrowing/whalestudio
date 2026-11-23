import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelEps

theorem isTateEps_tateEps_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (χ : kˣ →* ℂˣ), IsSmoothChar χ →
    IsTateEps ψ χ (tateEps ψ χ) ∧ tateEps ψ χ ≠ 0 := by
  intro k _ _ _ _ ψ hψ h1 χ hχ
  obtain ⟨⟨e, he, -⟩, hne⟩ := existsUnique_isTateEps ψ hψ h1 χ hχ
  have hx : ∃ e, IsTateEps ψ χ e := ⟨e, he⟩
  have hs : IsTateEps ψ χ (tateEps ψ χ) := by
    unfold tateEps
    rw [dif_pos hx]
    exact hx.choose_spec
  exact ⟨hs, hne _ hs⟩

end GlobalTheory.DelEps
