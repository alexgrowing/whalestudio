import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue

theorem UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), f i * f j = f j * f i) →
      ∀ (W : Submodule ℂ M),
        W ≠ ⊥ →
          (∀ (i : ι), ∀ y ∈ W, (f i : M → M) y ∈ W) →
            ∃ y ∈ W, y ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) y = c • y := by
  intro ι M _ _ _ f hc W hW hinv
  obtain ⟨V, ⟨hVW, hV0, hVinv⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ M)).has_min
      {V : Submodule ℂ M | V ≤ W ∧ V ≠ ⊥ ∧ ∀ i, ∀ y ∈ V, f i y ∈ V} ⟨W, le_rfl, hW, hinv⟩
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  refine ⟨y, hVW hyV, hy0, fun i => ?_⟩
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV0
  obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue ((f i).restrict (hVinv i) : Module.End ℂ V)
  obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
  have hv1 : f i (v : M) = c • (v : M) := by
    have h := congrArg Subtype.val hv.apply_eq_smul
    simpa using h
  have hv0 : (v : M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  refine ⟨c, ?_⟩
  by_contra hne
  refine hmin (V ⊓ (f i).eigenspace c) ⟨inf_le_left.trans hVW, ?_, ?_⟩ ?_
  · intro h
    have hm : (v : M) ∈ V ⊓ (f i).eigenspace c :=
      ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv1⟩
    rw [h] at hm
    exact hv0 ((Submodule.mem_bot ℂ).mp hm)
  · intro j z hz
    refine ⟨hVinv j z hz.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
    have hz2 : f i z = c • z := Module.End.mem_eigenspace_iff.mp hz.2
    have h : f i (f j z) = f j (f i z) := by
      rw [← Module.End.mul_apply, hc i j, Module.End.mul_apply]
    rw [h, hz2, map_smul]
  · refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have hm : y ∈ V ⊓ (f i).eigenspace c := by rw [h]; exact hyV
    exact Module.End.mem_eigenspace_iff.mp hm.2
