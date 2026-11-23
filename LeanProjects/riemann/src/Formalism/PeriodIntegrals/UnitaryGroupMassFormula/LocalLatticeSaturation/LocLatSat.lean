import Mathlib
import Formalism.PeriodIntegrals.LocLatSat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeSaturation.BcGSmulR

noncomputable section

open scoped nonZeroDivisors

namespace PI.LocLatSat.UnitaryGroupMassFormula

variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}

theorem steps {ι : Type*} [DecidableEq ι] (g : ι → (Fin n → K) →ₗ[K] K)
    (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) {x : Fin n → S} (hx : x ∈ latG φ O Λ)
    (T : Finset ι) (h0 : ∀ i ∈ T, fP φ (g i) x = 0) :
    x ∈ latG φ O (Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R) := by
  induction T using Finset.induction_on with
  | empty => simpa using hx
  | @insert a T ha ih =>
    have hx' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hfr : IsFractional R⁰ ((Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R).map
        ((g a).restrictScalars R)) := by
      have hfg : (Λ.map ((g a).restrictScalars R)).FG := hΛ.map _
      exact FractionalIdeal.isFractional_of_le (J := ⟨_, FractionalIdeal.isFractional_of_fg hfg⟩)
        (Submodule.map_mono inf_le_left)
    have hs := step φ O _ (g a) hfr hx' (h0 a (Finset.mem_insert_self a T))
    have e : Λ ⊓ ⨅ i ∈ insert a T, (LinearMap.ker (g i)).restrictScalars R =
        (Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R) ⊓
          (LinearMap.ker (g a)).restrictScalars R := by
      rw [Finset.iInf_insert]
      exact (inf_left_comm _ _ _).trans (inf_comm _ _)
    rw [e]
    exact hs

theorem sat (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) (W : Submodule K (Fin n → K)) :
    (latG φ O (Λ ⊓ W.restrictScalars R) : Set (Fin n → S)) =
      (latG φ O Λ : Set (Fin n → S)) ∩ Submodule.span S (bcG φ '' (W : Set (Fin n → K))) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨?_, ?_⟩
    · exact Submodule.span_mono (Set.image_mono (fun v hv => hv.1)) hx
    · have hle : Submodule.span O (bcG φ '' ((Λ ⊓ W.restrictScalars R : Submodule R _) : Set (Fin n → K))) ≤
          (Submodule.span S (bcG φ '' (W : Set (Fin n → K)))).restrictScalars O := by
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact Submodule.subset_span ⟨v, hv.2, rfl⟩
      exact hle hx
  · rintro x ⟨hxΛ, hxW⟩

    let b := Module.Basis.ofVectorSpace K W.dualAnnihilator
    haveI : Fintype (Module.Basis.ofVectorSpaceIndex K W.dualAnnihilator) := Fintype.ofFinite _
    let g : Module.Basis.ofVectorSpaceIndex K W.dualAnnihilator → (Fin n → K) →ₗ[K] K := fun i => (b i : Module.Dual K _)
    have hg : ∀ i w, w ∈ W → g i w = 0 := by
      intro i w hw
      exact (Submodule.mem_dualAnnihilator _).mp (b i).2 w hw
    have h0 : ∀ i ∈ (Finset.univ : Finset _), fP φ (g i) x = 0 := by
      intro i _
      have hle : Submodule.span S (bcG φ '' (W : Set (Fin n → K))) ≤ LinearMap.ker (fP φ (g i)) := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        show fP φ (g i) (bcG φ w) = 0
        rw [baseChange_apply_baseChange, hg i w hw, map_zero]
      exact hle hxW
    have hs := steps φ O g Λ hΛ hxΛ Finset.univ h0
    have hle2 : Λ ⊓ ⨅ i ∈ (Finset.univ : Finset _), (LinearMap.ker (g i)).restrictScalars R ≤
        Λ ⊓ W.restrictScalars R := by
      intro v hv
      refine ⟨hv.1, ?_⟩
      have hv2 : ∀ i, (b i : Module.Dual K (Fin n → K)) v = 0 := by
        intro i
        have h := (Submodule.mem_iInf _).mp ((Submodule.mem_inf.mp hv).2) i
        exact (Submodule.mem_iInf _).mp h (Finset.mem_univ i)
      show v ∈ W
      rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W), Submodule.mem_dualCoannihilator]
      intro ψ hψ
      have e := congrArg (fun d : W.dualAnnihilator => (d : Module.Dual K (Fin n → K)) v)
        (b.sum_repr ⟨ψ, hψ⟩)
      simp only at e
      rw [← e]
      rw [Submodule.coe_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Submodule.coe_smul, LinearMap.smul_apply, hv2, smul_zero]
    exact Submodule.span_mono (Set.image_mono hle2) hs

theorem locLatSat : PI.LocLatSat.Stmt := by
  intro F E _ _ _ _ _ sig p A n Λ W hΛ
  exact sat A.ιE A.O Λ hΛ W

end PI.LocLatSat.UnitaryGroupMassFormula
