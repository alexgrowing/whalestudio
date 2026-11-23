import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ULieDefs

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ULie
open scoped TensorProduct

private theorem UpperTheory.adjoin_apply_mem_of_invariant_submodule {V : Type} [AddCommGroup V] [Module ℂ V]
    (g : Set (Module.End ℂ V)) (U : Submodule ℂ V) (hU : ∀ b ∈ g, ∀ u ∈ U, b u ∈ U) :
    ∀ z ∈ Algebra.adjoin ℂ g, ∀ u ∈ U, z u ∈ U := by
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact hU x hx
  | algebraMap r =>
    intro u hu
    rw [Module.algebraMap_end_apply]
    exact U.smul_mem r hu
  | add x y _ _ hx hy =>
    intro u hu
    exact U.add_mem (hx u hu) (hy u hu)
  | mul x y _ _ hx hy =>
    intro u hu
    exact hx _ (hy u hu)

theorem UpperTheory.finiteDimensional_span_adjoin_apply_of_commuting_algebraic :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (s : Set (Module.End ℂ V)) (v : V), (∀ a ∈ s, ∀ b ∈ s, a * b = b * a) → FiniteDimensional ℂ (Submodule.span ℂ s) → (∀ a ∈ s, ∃ P : Polynomial ℂ, P ≠ 0 ∧ Polynomial.aeval a P v = 0) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z v) '' (Algebra.adjoin ℂ s : Subalgebra ℂ (Module.End ℂ V)))) := by
  intro V _ _ s v hcomm hfin hpoly
  classical
  let U : Set (Module.End ℂ V) → Submodule ℂ V := fun g =>
    Submodule.span ℂ ((fun z : Module.End ℂ V => z v) ''
      (Algebra.adjoin ℂ g : Subalgebra ℂ (Module.End ℂ V)))
  have hUinv : ∀ g : Set (Module.End ℂ V), ∀ b ∈ g, ∀ w ∈ U g, b w ∈ U g := by
    intro g b hb w hw
    have hle : U g ≤ (U g).comap b := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      show b (z v) ∈ U g
      exact Submodule.subset_span ⟨b * z, Subalgebra.mul_mem _ (Algebra.subset_adjoin hb) hz, rfl⟩
    exact hle hw
  have hvU : ∀ g : Set (Module.End ℂ V), v ∈ U g :=
    fun g => Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  have hind : ∀ t : Finset (Module.End ℂ V), (↑t : Set (Module.End ℂ V)) ⊆ s →
      FiniteDimensional ℂ (U ↑t) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hle : U ↑(∅ : Finset (Module.End ℂ V)) ≤ Submodule.span ℂ {v} := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        exact UpperTheory.adjoin_apply_mem_of_invariant_submodule _ _ (by simp) z hz v (Submodule.mem_span_singleton_self v)
      exact Submodule.finiteDimensional_of_le hle
    | insert a t hat ih =>
      intro hts
      rw [Finset.coe_insert, Set.insert_subset_iff] at hts
      haveI := ih hts.2
      obtain ⟨P, hP0, hPv⟩ := hpoly a hts.1
      set Q := Polynomial.C (P.leadingCoeff)⁻¹ * P with hQ
      have hQm : Q.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
        (inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hP0))
      have hac : ∀ z ∈ Algebra.adjoin ℂ (↑t : Set (Module.End ℂ V)), Commute a z := fun z hz =>
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz
          (fun b hb => hcomm a hts.1 b (hts.2 hb))
      have hker : ∀ w ∈ U ↑t, Polynomial.aeval a Q w = 0 := by
        intro w hw
        have hle : U ↑t ≤ LinearMap.ker (Polynomial.aeval a Q) := by
          rw [Submodule.span_le]
          rintro _ ⟨z, hz, rfl⟩
          have hc : Commute z (Polynomial.aeval a Q) :=
            Algebra.commute_of_mem_adjoin_singleton_of_commute
              (Polynomial.aeval_mem_adjoin_singleton ℂ a) (hac z hz).symm
          show Polynomial.aeval a Q (z v) = 0
          rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hQ, map_mul,
            Polynomial.aeval_C, Module.End.mul_apply, hPv, map_zero, map_zero]
        exact hle hw
      have hred : ∀ w ∈ U ↑t, (a ^ Q.natDegree) w =
          -∑ j ∈ Finset.range Q.natDegree, Q.coeff j • (a ^ j) w := by
        intro w hw
        have h0 := hker w hw
        simp only [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hQm.coeff_natDegree,
          one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply] at h0
        rw [eq_neg_iff_add_eq_zero, add_comm]
        simpa using h0
      let U' : Submodule ℂ V := ⨆ i : Fin Q.natDegree, (U ↑t).map (a ^ (i : ℕ))
      have hpow : ∀ j, ∀ w ∈ U ↑t, (a ^ j) w ∈ U' := by
        intro j
        induction j using Nat.strong_induction_on with
        | _ j ihj =>
          intro w hw
          by_cases hj : j < Q.natDegree
          · exact Submodule.mem_iSup_of_mem (⟨j, hj⟩ : Fin Q.natDegree)
              (Submodule.mem_map_of_mem hw)
          · have hsplit : (a ^ j) w = (a ^ (j - Q.natDegree)) ((a ^ Q.natDegree) w) := by
              rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel (not_lt.mp hj)]
            rw [hsplit, hred w hw, map_neg, map_sum]
            refine U'.neg_mem (U'.sum_mem (fun i hi => ?_))
            rw [map_smul, ← Module.End.mul_apply, ← pow_add]
            refine U'.smul_mem _ (ihj _ ?_ w hw)
            have := Finset.mem_range.mp hi
            omega
      have hU'a : ∀ u ∈ U', a u ∈ U' := by
        intro u hu
        refine Submodule.iSup_induction _ (motive := fun u => a u ∈ U') hu (fun i x hx => ?_) ?_
          (fun x y hx hy => ?_)
        · obtain ⟨w, hw, rfl⟩ := hx
          show a ((a ^ (i : ℕ)) w) ∈ U'
          rw [← Module.End.mul_apply, ← pow_succ']
          exact hpow _ w hw
        · simp
        · show a (x + y) ∈ U'
          rw [map_add]
          exact U'.add_mem hx hy
      have hU'b : ∀ b ∈ (↑t : Set (Module.End ℂ V)), ∀ u ∈ U', b u ∈ U' := by
        intro b hb u hu
        refine Submodule.iSup_induction _ (motive := fun u => b u ∈ U') hu (fun i x hx => ?_) ?_
          (fun x y hx hy => ?_)
        · obtain ⟨w, hw, rfl⟩ := hx
          show b ((a ^ (i : ℕ)) w) ∈ U'
          have hcb : Commute (a ^ (i : ℕ)) b := (hac b (Algebra.subset_adjoin hb)).pow_left _
          rw [← Module.End.mul_apply, ← hcb.eq, Module.End.mul_apply]
          exact hpow _ _ (hUinv _ b hb w hw)
        · simp
        · show b (x + y) ∈ U'
          rw [map_add]
          exact U'.add_mem hx hy
      have hle : U ↑(insert a t) ≤ U' := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        refine UpperTheory.adjoin_apply_mem_of_invariant_submodule _ U' ?_ z hz v ?_
        · intro b hb
          rw [Finset.coe_insert] at hb
          rcases hb with rfl | hb
          · exact hU'a
          · exact hU'b b hb
        · simpa using hpow 0 v (hvU _)
      exact Submodule.finiteDimensional_of_le hle
  obtain ⟨t, hts, -, hspan, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ s
  haveI := hind t hts
  refine Submodule.finiteDimensional_of_le (S₂ := U ↑t) ?_
  apply Submodule.span_mono
  apply Set.image_mono
  intro z hz
  refine (Algebra.adjoin_le (fun x hx => ?_)) hz
  apply Algebra.span_le_adjoin ℂ
  rw [hspan]
  exact Submodule.subset_span hx
