import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedRepEquivProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.ThK.MidJac

theorem isIrreducible_of_repEquiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (hρ : ρ.IsIrreducible) : ρ'.IsIrreducible := by
  let f : V ≃ₗ[ℂ] V' := e.toLinearEquiv
  have he : ∀ g v, f (ρ g v) = ρ' g (f v) := fun g v =>
    LinearMap.congr_fun (e.isIntertwining' g) v
  have he' : ∀ g v, f.symm (ρ' g v) = ρ g (f.symm v) := fun g v => by
    rw [f.symm_apply_eq, he, f.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (f : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (f.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (f : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (f : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective f.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

theorem detInd_irreducible_admissible : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x x' : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU α → GlobalTheory.KSplit.IsSmU β →
    (GlobalTheory.ThK.MidJac.detInd x x' α β).IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  intro hK k _ _ _ _ x x' α β hα hβ
  refine ⟨?_, GlobalTheory.ThK.MidJac.isAdmissible_detInd k x x' α β⟩
  obtain ⟨e⟩ := GlobalTheory.DetIndProd.detInd_equiv_prod₂ k x x' α β
  have h₁ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp (k := k) x hα.1 hα.2
  have h₂ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp (k := k) x' hβ.1 hβ.2
  have hP : (prod₂ (detRep (Fin x) α) (detRep (Fin x') β)).IsIrreducible :=
    hK.base.bernsteinUnitaryProductIrreducible k x x' ℂ ℂ _ _ h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  exact isIrreducible_of_repEquiv e.symm hP

end GlobalTheory.ThK.MidJac
