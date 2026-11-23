import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CuspRep.CompUniq

theorem isotypic : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  intro G H V W W' _ _ _ _ _ _ _ _ ρ s σ σ' hρ hσ hσ' hc f hf
  have hP : GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) = ⊤ := by
    rcases ((isIrreducible_iff ρ).1 hρ).2 (GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s)) (fun g v hv => by
      obtain ⟨u, hu⟩ := hc g
      have h1 := GlobalTheory.CuspRep.LocUniq.isoPart_comm σ (ρ.comp s) (ρ ((s u)⁻¹ * g)) (fun y x => by
        simp only [MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, (hu y).eq]) hv
      have h2 := GlobalTheory.CuspRep.LocUniq.isoPart_act σ (ρ.comp s) u h1
      rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h2) with h | h
    · refine absurd ?_ hf
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine LinearMap.ext fun v => ?_
      have h3 : f.toLinearMap v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) :=
        Submodule.mem_iSup_of_mem f ⟨v, rfl⟩
      rw [h] at h3
      rw [(Submodule.mem_bot ℂ).1 h3]
      rfl
    · exact h
  refine ⟨hP, fun f' hf' => ?_⟩
  haveI := hσ
  haveI := hσ'
  exact GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ σ' (ρ.comp s) hP f' hf'

end GlobalTheory.CuspRep.CompUniq
