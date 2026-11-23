import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem count_expand_map (c : ℕ → ℕ) (m k : ℕ) (K : List ℕ) (hK : K.Nodup) :
    (expand (K.map fun j => (c j, j))).count (m, k) = if m = 1 ∧ k ∈ K then c k else 0 := by
  induction K with
  | nil => simp [UpperTheory.Gal.InertialTypesAlt.expand]
  | cons a K ih =>
    rw [List.nodup_cons] at hK
    have ih' := ih hK.2
    simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.map_cons, List.flatMap_cons, List.count_append] at ih' ⊢
    rw [ih', List.count_replicate]
    by_cases hm : m = 1 <;> by_cases hk : k = a <;> simp_all <;> intros <;> subst_vars <;> simp_all

theorem UpperTheory.Gal.InertialTypesAlt.group1 :
    Group1 := by
  intro L₀ hpos
  have hmemK : ∀ k, k ∈ ((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup ↔ (1, k) ∈ L₀ := by
    intro k
    simp only [List.mem_dedup, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, hq1⟩, rfl⟩
      have hq' : q = (1, q.2) := Prod.ext (by simpa using hq1) rfl
      rw [← hq']
      exact hq
    · intro h
      exact ⟨(1, k), ⟨h, by simp⟩, rfl⟩
  refine ⟨(((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup).map fun j => (L₀.count (1, j), j),
    ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    have h1 : (1, j) ∈ L₀ := (hmemK j).1 hj
    exact ⟨List.count_pos_iff.2 h1, h1⟩
  · rw [List.map_map]
    simpa [Function.comp_def] using List.nodup_dedup ((L₀.filter fun p => p.1 = 1).map Prod.snd)
  · rw [List.perm_iff_count]
    rintro ⟨m, k⟩
    rw [List.count_append, count_expand_map _ m k _ (List.nodup_dedup _)]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hf : (m, k) ∉ L₀.filter (fun p => decide (2 ≤ p.1)) := by
        simp only [List.mem_filter, decide_eq_true_eq, not_and]
        intro _ h2
        omega
      rw [List.count_eq_zero_of_not_mem hf]
      interval_cases m
      · have h0 : (0, k) ∉ L₀ := fun h => absurd (hpos _ h) (lt_irrefl 0)
        simp [List.count_eq_zero_of_not_mem h0]
      · by_cases h : (1, k) ∈ L₀
        · simp [(hmemK k).2 h]
        · have h' : k ∉ ((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup :=
            fun hk => h ((hmemK k).1 hk)
          simp [h', List.count_eq_zero_of_not_mem h]
    · rw [List.count_filter (by simpa using hm)]
      have hm1 : m ≠ 1 := by omega
      simp [hm1]
