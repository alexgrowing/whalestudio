import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorMembership

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem list_prod_mem_of_forall {S : Submodule ℂ M} :
    ∀ (l : List (Module.End ℂ M)), (∀ f ∈ l, ∀ x ∈ S, f x ∈ S) → ∀ x ∈ S, l.prod x ∈ S
  | [], _, x, hx => by simpa using hx
  | f :: l, h, x, hx => by
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f List.mem_cons_self _
      (list_prod_mem_of_forall l (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hx)

theorem capEntry_mem {n : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    ∀ x ∈ S, Capelli.capEntry E t a b x ∈ S := by
  intro x hx
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS a b x hx) ?_
  split_ifs
  · simpa using S.smul_mem t hx
  · simp

theorem cminor_mem {n p : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (t : ℂ) :
    ∀ x ∈ S, Capelli.cminor E R C t x ∈ S := by
  intro x hx
  unfold Capelli.cminor
  rw [LinearMap.sum_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [LinearMap.smul_apply]
  refine S.smul_of_tower_mem _ ?_
  refine list_prod_mem_of_forall _ ?_ x hx
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact capEntry_mem hS _ _ _

end CapelliMinorMembership

open CapelliMinorMembership

theorem eig : EigStatement := by
  intro M _ _ m E S ω y β v hE hS hC hv
  have h0 : Capelli.capelliC E (ω : ℂ) v = 0 := hC v hv
  have eV : Capelli.eeV E = LemK.eeV E := by
    ext f d; simp [Capelli.eeV, LemK.eeV, LemK.prj]
  have eVd : Capelli.eeVd E = LemK.eeVd E := by
    ext f d; simp [Capelli.eeVd, LemK.eeVd, LemK.prj]
  constructor
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnPlus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eV,
        Capelli.capelliAPlus M m E y (ω : ℂ) v hE h0]
      simp
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnMinus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eVd,
        Capelli.capelliAMinus M m E β (ω : ℂ) v hE h0]
      simp

end ReciprocityTheory.ChartRestriction.DS.Lap
