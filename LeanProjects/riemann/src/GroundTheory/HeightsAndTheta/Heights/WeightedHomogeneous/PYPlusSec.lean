import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace YPlusSec

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

def newEmb : (Σ _ : Unit, Fin (D.size + 1)) → Coord D.extSizes := fun p ↦ ⟨none, p.2⟩

theorem newEmb_injective : Function.Injective (newEmb D) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  exact congrArg (Sigma.mk ()) (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem mapDomain_newEmb_none (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (j : Fin (D.extSizes none + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨none, j⟩ = m ⟨(), j⟩ :=
  Finsupp.mapDomain_apply (newEmb_injective D) m ⟨(), j⟩

theorem mapDomain_newEmb_some (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (k : ι)
    (i : Fin (D.extSizes (some k) + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨some k, i⟩ = 0 := by
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨p, hp⟩
  have h1 := congrArg (fun w : Coord D.extSizes ↦ w.1) hp
  simp [newEmb] at h1

end YPlusSec

open YPlusSec in

theorem YPlusSec.proof : YPlusSec.Statement := by
  intro ι _ _ n P D Ω _ y x' τ
  classical
  unfold Geo.secM
  congr 2
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range g (newEmb D) (newEmb_injective D) (by
      intro v hv
      rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
      obtain ⟨m, hm, hv⟩ := hv
      obtain ⟨o, i⟩ := v
      cases o with
      | none => exact ⟨⟨(), i⟩, rfl⟩
      | some k =>
        exfalso
        have h := hg m hm (some k)
        rw [Pi.single_eq_of_ne (Option.some_ne_none k), Finset.sum_eq_zero_iff] at h
        exact (Finsupp.mem_support_iff.mp hv) (h i (Finset.mem_univ _)))
    refine ⟨q, ?_, ?_⟩
    · intro m hm u
      cases u
      have hm' : Finsupp.mapDomain (newEmb D) m ∈ (rename (newEmb D) q).support := by
        rw [support_rename_of_injective (newEmb_injective D)]
        exact Finset.mem_image_of_mem _ hm
      have h := hg _ hm' none
      simp only [mapDomain_newEmb_none, Pi.single_eq_same] at h
      exact h
    · rw [aeval_rename]
      rfl
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rename (newEmb D) q, ?_, ?_⟩
    · intro m hm k
      rw [support_rename_of_injective (newEmb_injective D), Finset.mem_image] at hm
      obtain ⟨m, hm, rfl⟩ := hm
      cases k with
      | none =>
        simp only [mapDomain_newEmb_none, Pi.single_eq_same]
        exact hq m hm ()
      | some k =>
        simp only [mapDomain_newEmb_some, Finset.sum_const_zero]
        rw [Pi.single_eq_of_ne (Option.some_ne_none k)]
    · rw [aeval_rename]
      rfl

end

end GroundTheory.Heights₂.Heights
