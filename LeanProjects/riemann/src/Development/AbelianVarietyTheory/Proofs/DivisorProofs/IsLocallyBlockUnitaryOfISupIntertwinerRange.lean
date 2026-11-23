import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFinStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem locU_of_iSup_range_eq_top : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (G : Set (M →ₗ[ℂ] M')), (∀ f ∈ G, ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (⨆ f ∈ G, LinearMap.range f) = ⊤ → LocU s F → LocU s F' := by
  intro ι M _ _ _ _ s F M' _ _ F' G hG hsup hloc t
  classical
  have hy : ∀ y ∈ t, ∃ S : Finset G, y ∈ ⨆ i ∈ S, LinearMap.range (i : M →ₗ[ℂ] M') := by
    intro y _
    have h1 : y ∈ ⨆ i : G, LinearMap.range (i : M →ₗ[ℂ] M') := by
      rw [iSup_subtype'' G (fun f : M →ₗ[ℂ] M' => LinearMap.range f), hsup]; trivial
    exact Submodule.mem_iSup_iff_exists_finset.1 h1
  choose S hS using hy
  let SS : Finset G := t.attach.biUnion (fun y => S y.1 y.2)
  have hmem : ∀ y ∈ t, y ∈ ⨆ i ∈ SS, LinearMap.range (i : M →ₗ[ℂ] M') := by
    intro y hy
    exact (biSup_mono (fun i hi => Finset.mem_biUnion.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, hi⟩) :
      (⨆ i ∈ S y hy, LinearMap.range (i : M →ₗ[ℂ] M')) ≤ _) (hS y hy)
  let e : SS ≃ Fin SS.card := SS.equivFin
  let f : Fin SS.card → (M →ₗ[ℂ] M') := fun k => ((e.symm k).1 : M →ₗ[ℂ] M')
  let g : (Fin SS.card → M) →ₗ[ℂ] M' := ∑ k, f k ∘ₗ LinearMap.proj k
  have hg : ∀ x, g x = ∑ k, f k (x k) := by intro x; simp [g]
  have hrange : ∀ y ∈ t, y ∈ LinearMap.range g := by
    intro y hy
    refine (iSup₂_le ?_ : (⨆ i ∈ SS, LinearMap.range (i : M →ₗ[ℂ] M')) ≤ LinearMap.range g) (hmem y hy)
    intro i hi w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hw
    refine ⟨Pi.single (e ⟨i, hi⟩) x, ?_⟩
    rw [hg, Finset.sum_eq_single (e ⟨i, hi⟩)]
    · simp [f]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  choose z hz using fun y hy => LinearMap.mem_range.1 (hrange y hy)
  obtain ⟨U, hU, hUU⟩ := GlobalTheory.T.isLocallyBlockUnitary_pi_fin ι M s F hloc SS.card (t.attach.image fun y : {x // x ∈ t} => z y.1 y.2)
  refine ⟨U.map g, ?_, GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner ι (Fin SS.card → M) s _ M' F' g U ?_ hUU⟩
  · intro y hy
    exact ⟨z y hy, hU _ (Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩), hz y hy⟩
  · intro a b hab x _
    rw [hg, hg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact hG (f k) (e.symm k).1.2 a b hab (x k)

example : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (G : Set (M →ₗ[ℂ] M')), (∀ f ∈ G, ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (⨆ f ∈ G, LinearMap.range f) = ⊤ → LocU s F → LocU s F' := locU_of_iSup_range_eq_top

end GlobalTheory.HoweR
