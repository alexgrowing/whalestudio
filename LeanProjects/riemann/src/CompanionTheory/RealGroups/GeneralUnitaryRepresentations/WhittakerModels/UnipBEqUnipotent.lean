import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import GroundTheory.AutomorphicForms.ContragredientTranspose

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace CompanionTheory.rg.gu.whit

theorem unipB_eq_unipotent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n := by
  ext g
  rw [mem_unipB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 i j hij, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 hij, h2⟩

theorem whitChar_eq_psiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)) :
    ((whitChar ψ n u : ℂˣ) : ℂ) =
      GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) := by
  have hs : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin n) k).val p.1 p.2) =
      GroundTheory.Automorphic.Whittaker.superdiagSum ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rfl
  show ((Circle.toUnits (ψ _) : ℂˣ) : ℂ) = ((ψ (GroundTheory.Automorphic.Whittaker.superdiagSum _) : Circle) : ℂ)
  rw [hs]
  rfl

theorem isAdmissible_iff {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) : GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  have hfix : ∀ K : Subgroup G, fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
    intro K
    ext v
    constructor
    · intro h g hg
      have := h ⟨g, hg⟩
      simpa using this
    · intro h g
      have := h g g.2
      simpa using this
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun K hc ho => hfix K ▸ h2 K ho hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun K ho hc => (hfix K).symm ▸ h2 K hc ho⟩

end CompanionTheory.rg.gu.whit
