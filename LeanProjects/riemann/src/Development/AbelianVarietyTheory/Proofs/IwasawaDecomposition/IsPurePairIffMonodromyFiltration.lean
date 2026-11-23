import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Graded

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U : ℤ → Submodule K V}
  {N : End K V}

theorem exists_proj_of_iSupIndep (hi : iSupIndep U) (ht : ⨆ i, U i = ⊤) :
    ∃ p : ℤ → End K V, (∀ d v, p d v ∈ U d) ∧ (∀ d, ∀ v ∈ U d, p d v = v) ∧
      (∀ d e, e ≠ d → ∀ v ∈ U e, p d v = 0) ∧
      ∀ (S : Submodule K V) (v : V), (∀ d, p d v ∈ S) → v ∈ S := by
  classical
  let := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ht).chooseDecomposition
  refine ⟨fun d => (U d).subtype ∘ₗ DirectSum.component K ℤ (fun i => U i) d ∘ₗ
    (DirectSum.decomposeLinearEquiv U).toLinearMap, fun d v => Subtype.coe_prop _,
    fun d v hv => DirectSum.decompose_of_mem_same U hv,
    fun d e hed v hv => DirectSum.decompose_of_mem_ne U hv hed, fun S v hv => ?_⟩
  rw [← DirectSum.sum_support_decompose U v]
  exact S.sum_mem fun d _ => hv d

theorem pow_mem_of_degree_two (hN : ∀ d, ∀ v ∈ U d, N v ∈ U (d + 2)) (m : ℕ) {d e : ℤ}
    (he : e = d + 2 * m) {v : V} (hv : v ∈ U d) : (N ^ m) v ∈ U e := by
  subst he
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', End.mul_apply]
    have := hN _ _ ih
    rwa [show d + 2 * (m : ℤ) + 2 = d + 2 * ((m + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem eq_zero_of_pow_eq_zero (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d : ℤ}
    (hd : d + m ≤ 0) {v : V} (hv : v ∈ U d) (h0 : (N ^ m) v = 0) : v = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = -((c + m : ℕ) : ℤ) := ⟨(-d - m).toNat, by omega⟩
  subst hc
  refine (hb (c + m)).2.1 hv (zero_mem _) ?_
  rw [pow_add, End.mul_apply, h0, map_zero, map_zero]

theorem exists_pow_eq (hN : ∀ d, ∀ v ∈ U d, N v ∈ U (d + 2))
    (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d e : ℤ}
    (hd : (m : ℤ) ≤ d) (he : d = e + 2 * m) {v : V} (hv : v ∈ U d) :
    ∃ u ∈ U e, (N ^ m) u = v := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = ((m + c : ℕ) : ℤ) := ⟨(d - m).toNat, by omega⟩
  rw [hc] at hv
  obtain ⟨u, hu, rfl⟩ := (hb (m + c)).2.2 hv
  refine ⟨(N ^ c) u, pow_mem_of_degree_two hN c (by omega) hu, ?_⟩
  rw [pow_add, End.mul_apply]

end Graded

theorem iSupIndep_absSpace {V ι : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V) {r : ι → ℝ}
    (hr : Function.Injective r) : iSupIndep fun i => absSpace f (r i) := by
  intro i
  refine ((End.eigenspaces_iSupIndep f).disjoint_biSup_biSup (s := {α | ‖α‖ = r i})
    (t := {α | ‖α‖ ≠ r i}) disjoint_compl_right).mono_right ?_
  refine iSup₂_le fun j hj => iSup₂_le fun α hα => le_iSup₂_of_le α ?_ le_rfl
  exact fun h => hj (hr (hα.symm.trans h))

end GlobalTheory.WeilDeligne
