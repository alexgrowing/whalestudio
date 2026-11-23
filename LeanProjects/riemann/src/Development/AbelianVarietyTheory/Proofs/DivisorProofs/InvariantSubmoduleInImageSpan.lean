import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMemSpanRangeLeOfIsSimpleModule

namespace GlobalTheory

open Representation

theorem mem_span_equivariant_into_of_mem_imgSpan :
    ∀ (G U W : Type) [Group G] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G U) (ρ : Representation ℂ G W), π.IsIrreducible →
    ∀ M : Submodule ℂ W, (∀ g, ∀ w ∈ M, ρ g w ∈ M) → ∀ w ∈ M, w ∈ GlobalTheory.LocTypeGood.imgSpan π ρ →
      w ∈ Submodule.span ℂ {y | ∃ T : U →ₗ[ℂ] W, (∀ g, T ∘ₗ π g = ρ g ∘ₗ T) ∧ (∀ u, T u ∈ M) ∧ ∃ u, y = T u} := by
  intro G U W _ _ _ _ _ π ρ hπ M hM w hwM hw
  have hS : IsSimpleModule (MonoidAlgebra ℂ G) π.asModule :=
    (irreducible_iff_isSimpleModule_asModule π).mp hπ
  let Φ := IntertwiningMap.equivLinearMapAsModule π ρ
  let Q : W → Prop := fun x => ∃ n : ℕ, ∃ T : Fin n → (π.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule),
      ∃ ξ : Fin n → π.asModule, x = ∑ i, T i (ξ i)
  have h0 : Q 0 := ⟨0, Fin.elim0, Fin.elim0, by simp <;> rfl⟩
  have hadd : ∀ x y, Q x → Q y → Q (x + y) := by
    rintro x y ⟨n, T₁, ξ₁, rfl⟩ ⟨m, T₂, ξ₂, rfl⟩
    exact ⟨n + m, Fin.append T₁ T₂, Fin.append ξ₁ ξ₂, by simp [Fin.sum_univ_add] <;> rfl⟩
  have hsum : Q w := by
    unfold GlobalTheory.LocTypeGood.imgSpan at hw
    refine Submodule.iSup_induction _ (motive := Q) hw (fun T x hx => ?_) h0 hadd
    refine Submodule.iSup_induction _ (motive := Q) hx (fun h x hx => ?_) h0 hadd
    obtain ⟨u, rfl⟩ := hx
    exact ⟨1, fun _ => Φ ⟨T, h⟩, fun _ => u, by simp; rfl⟩
  obtain ⟨n, T, ξ, hwT⟩ := hsum
  let S : Subrepresentation ρ := ⟨M, fun g v hv => hM g v hv⟩
  let N : Submodule (MonoidAlgebra ℂ G) ρ.asModule := S.asSubmodule
  have hN : ∑ i, T i (ξ i) ∈ N := by rw [← hwT]; exact hwM
  have key := sum_mem_span_range_le_of_isSimpleModule (MonoidAlgebra ℂ G) π.asModule ρ.asModule hS n T ξ N hN
  rw [← hwT] at key
  clear hwM hw hwT
  induction key using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, y, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨(Φ.symm F).toLinearMap, fun g => (Φ.symm F).isIntertwining' g,
      fun u => hF ⟨u, rfl⟩, y, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory
