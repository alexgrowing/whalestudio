import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR

theorem tprod_cyclic_top : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  intro T _ _ V _ _ R S a C v hgen N hN hC hv
  have key : ∀ s : Finset T, ∀ f : ∀ w, V w, (∀ w, w ∉ s → f w = v w) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = v := funext fun w => hf w (Finset.notMem_empty w)
      rw [this]; exact hv
    | insert w s hws ih =>
      intro f hf
      let K : Submodule ℂ (V w) :=
        Submodule.comap ((PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) N
      have hmem : ∀ x, x ∈ K ↔ PiTensorProduct.tprod ℂ (Function.update f w x) ∈ N := by
        intro x; simp [K, MultilinearMap.toLinearMap_apply]
      have hstab : ∀ Z, ∀ y ∈ K, a w Z y ∈ K := by
        intro Z y hy
        rw [hmem] at hy ⊢
        have h1 := hN w Z _ hy
        rw [actAt_apply, atPl, PiTensorProduct.map_tprod] at h1
        convert h1 using 2
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Function.update_of_ne h]
      have hvK : v w ∈ K := by
        rw [hmem]
        apply ih
        intro u hu
        by_cases h : u = w
        · subst h; simp
        · rw [Function.update_of_ne h]
          exact hf u (by simp [h, hu])
      have hCK : C w ≤ K := by
        intro c hc
        rw [hmem]
        apply hC
        apply Submodule.subset_span
        exact ⟨Function.update f w c, ⟨w, by simpa using hc⟩, rfl⟩
      have hgK : genSub (a w) {v w} ≤ K := by
        apply sInf_le
        refine ⟨?_, hstab⟩
        simpa using hvK
      have htop : K = ⊤ := by
        rw [eq_top_iff, ← hgen w]
        exact sup_le hgK hCK
      have : f w ∈ K := by rw [htop]; trivial
      rw [hmem, Function.update_eq_self] at this
      exact this
  have hall : ∀ f : ∀ w, V w, PiTensorProduct.tprod ℂ f ∈ N :=
    fun f => key Finset.univ f (fun w hw => absurd (Finset.mem_univ w) hw)
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact hall f

end GlobalTheory.HoweR
