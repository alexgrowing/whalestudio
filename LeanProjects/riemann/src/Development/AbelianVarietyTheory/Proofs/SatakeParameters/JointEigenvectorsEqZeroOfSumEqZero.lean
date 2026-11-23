import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem joint_eigenvectors_eq_zero_of_sum_eq_zero (ι κ M : Type) [AddCommGroup M] [Module ℂ M]
    (A : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (v : κ → M) (s : Finset κ)
    (heig : ∀ k ∈ s, ∀ i, A i (v k) = χ k i • v k) (hinj : Set.InjOn χ s)
    (hsum : ∑ k ∈ s, v k = 0) : ∀ k ∈ s, v k = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert a s ha ih =>
    have hsum' : v a + ∑ k ∈ s, v k = 0 := by rwa [Finset.sum_insert ha] at hsum
    have hs : ∀ k ∈ s, v k = 0 := by
      intro k hk
      have hne : χ k ≠ χ a := by
        intro h
        have hka : k = a := hinj (by simp [hk]) (by simp) h
        exact ha (hka ▸ hk)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hw : (χ k i - χ a i) • v k = 0 := by
        refine ih (fun j => (χ j i - χ a i) • v j) ?_ ?_ ?_ k hk
        · intro j hj i'
          have h1 := heig j (Finset.mem_insert_of_mem hj) i'
          simp only [map_smul, h1]
          rw [smul_comm]
        · exact hinj.mono (by simp)
        · have h2 : A i (v a + ∑ k ∈ s, v k) - χ a i • (v a + ∑ k ∈ s, v k) = 0 := by
            rw [hsum']; simp
          rw [map_add, map_sum, heig a (Finset.mem_insert_self a s) i, smul_add, Finset.smul_sum,
            add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [heig j (Finset.mem_insert_of_mem hj) i, sub_smul]
      exact (smul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hi)
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa [Finset.sum_eq_zero hs] using hsum'
    · exact hs k hk

end GlobalTheory
