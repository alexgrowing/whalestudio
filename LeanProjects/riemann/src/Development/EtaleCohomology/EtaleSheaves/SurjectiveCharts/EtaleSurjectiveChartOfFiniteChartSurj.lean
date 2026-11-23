import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts

noncomputable section

namespace LateralTheory.E.LSurjChartPf

theorem bij_iff {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (S : Subalgebra A A') (r : S) :
    Function.Bijective (Localization.awayMap S.val.toRingHom r) ↔ ∀ x : A', ∃ m : ℕ, r.1 ^ m * x ∈ S := by
  rw [Function.Bijective, and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective),
    Localization.awayMap_surjective_iff]
  constructor
  · intro H x
    obtain ⟨b, m, e⟩ := H x
    refine ⟨m, ?_⟩
    have e' : (b : A') = r.1 ^ m * x := e
    rw [← e']; exact b.2
  · intro H x
    obtain ⟨m, hm⟩ := H x
    exact ⟨⟨_, hm⟩, m, rfl⟩

theorem fg_sup {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] {ι : Type} (s : Finset ι)
    (S : ι → Subalgebra A A') (h : ∀ i ∈ s, (S i).toSubmodule.FG) : (s.sup S).toSubmodule.FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, Algebra.toSubmodule_bot]; rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton 1
  | insert a s ha ih =>
    rw [Finset.sup_insert, ← Subalgebra.mul_toSubmodule]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem graphPatch : GraphPatch := by
  intro A _ I A' _ _ φ H
  classical
  let T : Set A' := {h | ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧ h ∈ S' ∧ ∀ x : A', ∃ m : ℕ, h ^ m * x ∈ S'}
  have htop : Ideal.span T ⊔ RingHom.ker φ = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨S', hfg, r, hr, hb⟩ := H q hq.isPrime (le_trans le_sup_right hle)
    exact hr (hle (Ideal.mem_sup_left (Ideal.subset_span ⟨S', hfg, r.2, (bij_iff S' r).mp hb⟩)))
  have h1 : (1 : A') ∈ Ideal.span T ⊔ RingHom.ker φ := by rw [htop]; trivial
  obtain ⟨y, hy, k, hk, hyk⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, hsT, hys⟩ := Submodule.mem_span_finite_of_mem_span hy
  obtain ⟨c, -, hc⟩ := (Submodule.mem_span_finset).mp hys
  have hT : ∀ h ∈ s, ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧ h ∈ S' ∧
      ∀ x : A', ∃ m : ℕ, h ^ m * x ∈ S' := fun h hh => hsT hh
  choose! Sh hfg hmem hx using hT
  choose! m hm using hx
  choose a ha using fun h : A' => Ideal.Quotient.mk_surjective (I := I) (φ (c h))
  let S := s.sup Sh
  have hS : ∀ h ∈ s, h ∈ S := fun h hh => (Finset.le_sup (f := Sh) hh) (hmem h hh)
  let f : A' → S := fun h => if hh : h ∈ S then ⟨algebraMap A A' (a h) * h, S.mul_mem (S.algebraMap_mem _) hh⟩ else 0
  have hf : ∀ h ∈ s, (f h : A') = algebraMap A A' (a h) * h := fun h hh => by simp [f, hS h hh]
  let r : S := ∑ h ∈ s, f h
  have hr : (r : A') = ∑ h ∈ s, algebraMap A A' (a h) * h := by
    show S.val (∑ h ∈ s, f h) = _
    rw [map_sum]
    exact Finset.sum_congr rfl hf
  refine ⟨S, fg_sup s Sh hfg, r, ?_, ?_⟩
  · have : φ r.1 = 1 := by
      rw [hr, map_sum]
      have e1 : φ y = 1 := by
        have : φ k = 0 := hk
        rw [← map_one φ, ← hyk, map_add, this, add_zero]
      rw [← e1, ← hc, map_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, AlgHom.commutes, smul_eq_mul, map_mul]
      simp [Ideal.Quotient.algebraMap_eq, ha]
    rw [this]; exact isUnit_one
  · rw [bij_iff]
    intro x
    let n := s.sup (fun h => m h x)
    have hpow : ∀ h ∈ s, h ^ n * x ∈ S := fun h hh => by
      have hle : m h x ≤ n := Finset.le_sup (f := fun h => m h x) hh
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact S.mul_mem (S.pow_mem (hS h hh) _) ((Finset.le_sup (f := Sh) hh) (hm h hh x))
    let K : Ideal S :=
      { carrier := {z | z.1 * x ∈ S}
        add_mem' := fun {u v} hu hv => by
          simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_mul] at *; exact S.add_mem hu hv
        zero_mem' := by simp
        smul_mem' := fun u v hv => by
          simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc] at *
          exact S.mul_mem u.2 hv }
    have hspan : Ideal.span ((fun h => f h ^ (n + 1)) '' (s : Set A')) ≤ K := by
      rw [Ideal.span_le]
      rintro _ ⟨h, hh, rfl⟩
      show ((f h ^ (n + 1) : S) : A') * x ∈ S
      rw [SubmonoidClass.coe_pow, hf h hh, mul_pow, mul_assoc]
      refine S.mul_mem (S.pow_mem (S.algebraMap_mem _) _) ?_
      rw [pow_succ', mul_assoc]; exact S.mul_mem (hS h hh) (hpow h hh)
    exact ⟨s.card * n + 1, by
      have := hspan (Ideal.sum_pow_mem_span_pow s f n)
      simpa [K, r] using this⟩

theorem etale_surjective_chart_of_finite_chart_surj (hB : FiniteChartSurj) : LateralTheory.E.LChartPf.LSurjChart :=
  LSurjChart_of graphPatch hB

end LateralTheory.E.LSurjChartPf
