import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ContrSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.autOf :
    UpperTheory.V.Cj.H.AutOf := by
  intro E _ _ _ a U hU Ξ m q ω hω X i hc hg
  have hl := (UpperTheory.V.Cj.H.levLin E a U Ξ q).2.2.1 ω hω X i
  obtain ⟨W, _, _, _, ρ, -, hρ⟩ := UpperTheory.V.Cj.H.kType E a Ξ q
  obtain ⟨T, w, hT, hw⟩ := hρ ω hω.equiv X i
  generalize cmp i (ω X) = φ at hc hg hl hw ⊢
  refine ⟨hl.1, ?_, ?_, ?_, hg⟩
  · exact Subgroup.isOpen_mono (H₁ := U)
      (H₂ := { carrier := {k | finRep E a k φ = φ}
               one_mem' := by simp
               mul_mem' := fun {x y} hx hy => by
                 rw [Set.mem_setOf_eq] at hx hy ⊢
                 rw [map_mul, Module.End.mul_apply, hy, hx]
               inv_mem' := fun {x} hx => by
                 rw [Set.mem_setOf_eq] at hx ⊢
                 conv_lhs => rw [← hx]
                 rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] })
      (fun u hu => hl.2.1 u hu) hU
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ k w, by rw [hT, hw]⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have key : ∃ c : ℂ, z φ = c • φ := by
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨t, u, rfl⟩ := hx
        exact ⟨_, hc t u⟩
      | algebraMap c => exact ⟨c, rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨c + d, by rw [LinearMap.add_apply, hx, hy, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨d * c, by rw [Module.End.mul_apply, hy, map_smul, hx, mul_smul]⟩
    obtain ⟨c, h⟩ := key
    exact Submodule.mem_span_singleton.2 ⟨c, h.symm⟩
