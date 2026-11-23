import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepC

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs.StrStepD

def strSet (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) : Set ℝ :=
  {x | (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨ ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j}

theorem mem_strSet {c₁ c₂ x : ℝ} {d₁ d₂ : ℕ} :
    x ∈ strSet c₁ c₂ d₁ d₂ ↔ (∃ i : Fin d₁, x = c₁ + spehExp d₁ i) ∨ ∃ j : Fin d₂, x = c₂ + spehExp d₂ j := by
  simp only [strSet, Set.mem_setOf_eq, spehExp]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨⟨i, hi⟩, by simp only; ring⟩
    · exact Or.inr ⟨⟨j, hj⟩, by simp only; ring⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨i, i.2, by ring⟩
    · exact Or.inr ⟨j, j.2, by ring⟩

theorem of_infChar (m m₀ : Multiset ℂ) {d₁ d₂ : ℕ} (c₁ c₂ : ℝ)
    (hm : m = (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + (c₁ : ℂ)) +
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + (c₂ : ℂ)))
    (hne : m₀ ≠ 0) (hnd : m.Nodup) (hint : ∀ x ∈ m, ∀ y ∈ m, ∃ n : ℤ, x - y = n) :
    (∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j) ∧
      ∀ u ∈ strSet c₁ c₂ d₁ d₂, ∀ v ∈ strSet c₁ c₂ d₁ d₂, ∃ n : ℤ, u - v = n := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 : ∀ i : Fin d₁, t + (spehExp d₁ i : ℂ) + c₁ ∈
      (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + (c₁ : ℂ)) := fun i =>
    Multiset.mem_map.2 ⟨t + spehExp d₁ i, Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Multiset.mem_map.2 ⟨t, ht, rfl⟩⟩, rfl⟩
  have h2 : ∀ j : Fin d₂, t + (spehExp d₂ j : ℂ) + c₂ ∈
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + (c₂ : ℂ)) := fun j =>
    Multiset.mem_map.2 ⟨t + spehExp d₂ j, Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, Multiset.mem_map.2 ⟨t, ht, rfl⟩⟩, rfl⟩
  have hnd' := hm ▸ hnd
  rw [Multiset.nodup_add] at hnd'
  have key : ∀ u ∈ strSet c₁ c₂ d₁ d₂, t + (u : ℂ) ∈ m := by
    intro u hu
    rw [mem_strSet] at hu
    rw [hm]
    rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine Multiset.mem_add.2 (Or.inl ?_)
      convert h1 i using 1
      push_cast; ring
    · refine Multiset.mem_add.2 (Or.inr ?_)
      convert h2 j using 1
      push_cast; ring
  refine ⟨fun i j hi hj e => ?_, fun u hu v hv => ?_⟩
  · have e' : t + (spehExp d₁ ⟨i, hi⟩ : ℂ) + c₁ = t + (spehExp d₂ ⟨j, hj⟩ : ℂ) + c₂ := by
      have e2 := congrArg (fun r : ℝ => (r : ℂ)) e
      simp only [spehExp] at e2 ⊢
      push_cast at e2 ⊢
      linear_combination e2
    exact Multiset.disjoint_left.1 hnd'.2.2 (h1 ⟨i, hi⟩) (e' ▸ h2 ⟨j, hj⟩)
  · obtain ⟨n, hn⟩ := hint _ (key u hu) _ (key v hv)
    refine ⟨n, ?_⟩
    have : ((u - v : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; linear_combination hn
    exact_mod_cast this

theorem mem_sat (q : ℂ) (B : Multiset ℂ) {d₁ d₂ : ℕ} (c₁ c₂ : ℝ) (z : ℂ) :
    z ∈ (∑ i : Fin d₁, B.map (fun b => b * q ^ (-((c₁ : ℂ) + (spehExp d₁ i : ℂ))))) +
        ∑ j : Fin d₂, B.map (fun b => b * q ^ (-((c₂ : ℂ) + (spehExp d₂ j : ℂ)))) ↔
      ∃ x ∈ strSet c₁ c₂ d₁ d₂, ∃ β ∈ B, z = β * q ^ (-(x : ℂ)) := by
  simp only [Multiset.mem_add, Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_map, mem_strSet]
  constructor
  · rintro (⟨i, β, hβ, rfl⟩ | ⟨j, β, hβ, rfl⟩)
    · exact ⟨c₁ + spehExp d₁ i, Or.inl ⟨i, rfl⟩, β, hβ, by push_cast; rfl⟩
    · exact ⟨c₂ + spehExp d₂ j, Or.inr ⟨j, rfl⟩, β, hβ, by push_cast; rfl⟩
  · rintro ⟨x, (⟨i, rfl⟩ | ⟨j, rfl⟩), β, hβ, rfl⟩
    · exact Or.inl ⟨i, β, hβ, by push_cast; rfl⟩
    · exact Or.inr ⟨j, β, hβ, by push_cast; rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem match_left {a₁ a₂ d₁ d₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂)
    (hn₁ : IsNormalised π₁) (hn₂ : IsNormalised π₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ)
    (hp : (StrStepC.twL π₁ π₂ x y).Perm (StrStepC.twL π₁ π₂ (fun i => -conj (x i)) (fun j => -conj (y j))))
    (i : Fin d₁) :
    (∃ i', x i = -conj (x i')) ∨
      ∃ j, x i = -conj (y j) ∧ (⟨a₁, CG.mk π₁⟩ : Σ b, CG E b) = ⟨a₂, CG.mk π₂⟩ := by
  have hmem : (⟨a₁, (CG.mk π₁).twist (GlobalTheory.CuspRep.Model.absC E (x i))⟩ : Σ b, CG E b) ∈ StrStepC.twL π₁ π₂ x y :=
    List.mem_append.2 (Or.inl (List.mem_ofFn.2 ⟨i, rfl⟩))
  rcases List.mem_append.1 (hp.mem_iff.1 hmem) with h | h
  · obtain ⟨i', hi'⟩ := List.mem_ofFn.1 h
    exact Or.inl ⟨i', (StrStepB.match_twist ha₁ π₁ π₁ hn₁ hn₁ hi'.symm).1⟩
  · obtain ⟨j, hj⟩ := List.mem_ofFn.1 h
    obtain ⟨e1, e2⟩ := StrStepB.match_twist ha₁ π₁ π₂ hn₁ hn₂ hj.symm
    exact Or.inr ⟨j, e1, e2⟩

theorem match_right {a₁ a₂ d₁ d₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂)
    (hn₁ : IsNormalised π₁) (hn₂ : IsNormalised π₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ)
    (hp : (StrStepC.twL π₁ π₂ x y).Perm (StrStepC.twL π₁ π₂ (fun i => -conj (x i)) (fun j => -conj (y j))))
    (j : Fin d₂) :
    (∃ j', y j = -conj (y j')) ∨
      ∃ i, y j = -conj (x i) ∧ (⟨a₂, CG.mk π₂⟩ : Σ b, CG E b) = ⟨a₁, CG.mk π₁⟩ := by
  have hmem : (⟨a₂, (CG.mk π₂).twist (GlobalTheory.CuspRep.Model.absC E (y j))⟩ : Σ b, CG E b) ∈ StrStepC.twL π₁ π₂ x y :=
    List.mem_append.2 (Or.inr (List.mem_ofFn.2 ⟨j, rfl⟩))
  rcases List.mem_append.1 (hp.mem_iff.1 hmem) with h | h
  · obtain ⟨i, hi⟩ := List.mem_ofFn.1 h
    obtain ⟨e1, e2⟩ := StrStepB.match_twist ha₂ π₂ π₁ hn₂ hn₁ hi.symm
    exact Or.inr ⟨i, e1, e2⟩
  · obtain ⟨j', hj'⟩ := List.mem_ofFn.1 h
    exact Or.inl ⟨j', (StrStepB.match_twist ha₂ π₂ π₂ hn₂ hn₂ hj'.symm).1⟩

end PositivityTheory.Rg.Rs.StrStepD

end
