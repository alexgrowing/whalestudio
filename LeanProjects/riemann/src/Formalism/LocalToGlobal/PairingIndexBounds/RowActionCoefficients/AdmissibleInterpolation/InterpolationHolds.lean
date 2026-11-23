import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.WeylComplementInDetCoeffSpan

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

theorem interpolation_holds : Interp := by
  intro K τ W _ _ _ _ S w h m hm
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ (w m) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff K (w m)).1 hcon)
  let P : MvPolynomial τ K := ∑ m' ∈ S, monomial m' (φ (w m'))
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    have := congrArg φ (h x)
    rw [map_sum, map_zero] at this
    rw [map_zero, map_sum, ← this]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, mul_comm]
  have hc : coeff m P = φ (w m) := by
    classical
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq' S m]
    rw [if_pos hm]
  rw [hP, coeff_zero] at hc
  exact hφ hc.symm

theorem prod_span {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A] (S : ι → Set A)
    (T : Submodule R A) (h : ∀ f : ι → A, (∀ i, f i ∈ S i) → ∏ i, f i ∈ T) :
    ∀ f : ι → A, (∀ i, f i ∈ Submodule.span R (S i)) → ∏ i, f i ∈ T := by
  have key : ∀ (s : Finset ι) (f : ι → A), (∀ i ∈ s, f i ∈ Submodule.span R (S i)) → (∀ i ∉ s, f i ∈ S i) → ∏ i, f i ∈ T := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro f _ h2; exact h f fun i => h2 i (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro f h1 h2
      have hfa := h1 a (Finset.mem_insert_self a s)
      have hup : ∀ z : A, ∏ i, Function.update f a z i = z * ∏ i ∈ Finset.univ.erase a, f i := by
        intro z
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hgen : ∀ z ∈ Submodule.span R (S a), z * ∏ i ∈ Finset.univ.erase a, f i ∈ T := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          rw [← hup]
          apply ih
          · intro i hi
            have : i ≠ a := fun e => ha (e ▸ hi)
            rw [Function.update_of_ne this]
            exact h1 i (Finset.mem_insert_of_mem hi)
          · intro i hi
            by_cases e : i = a
            · subst e; rw [Function.update_self]; exact hz
            · rw [Function.update_of_ne e]
              exact h2 i fun hh => (Finset.mem_insert.1 hh).elim e hi
        | zero => rw [zero_mul]; exact T.zero_mem
        | add x y _ _ hx hy => rw [add_mul]; exact T.add_mem hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact T.smul_mem c hx
      have := hgen (f a) hfa
      rwa [Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at this
  intro f hf
  exact key Finset.univ f (fun i _ => hf i) fun i hi => absurd (Finset.mem_univ i) hi

end Formalism.L2.PairingIndexBounds.Ent
