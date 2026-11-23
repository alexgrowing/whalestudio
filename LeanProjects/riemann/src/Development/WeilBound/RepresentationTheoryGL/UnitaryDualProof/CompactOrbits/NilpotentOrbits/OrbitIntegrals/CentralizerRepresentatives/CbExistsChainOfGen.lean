import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbIsChainApply

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem cb_exists_chain_of_gen (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (y : ι → W)
    (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (hy : ∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) :
    ∃ B : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B ∧ ∀ p, B p = cbFam N l y p := by
  set S := span E (Set.range (cbFam N l y)) with hSdef
  have hS : ∀ x ∈ S, N x ∈ S := by
    intro x hx
    have : S ≤ S.comap N := by
      rw [hSdef, span_le]
      rintro _ ⟨p, rfl⟩
      show N (cbFam N l y p) ∈ S
      simp only [cbFam]
      rw [cb_pow_succ]
      by_cases h : (p.2 : ℕ) + 1 < l p.1
      · exact subset_span ⟨⟨p.1, ⟨p.2 + 1, h⟩⟩, rfl⟩
      · rw [cb_pow_zero_of_le N (hy0 p.1) (by omega)]; exact S.zero_mem
    exact this hx
  have htop : S ⊔ LinearMap.range N = ⊤ := by
    rw [eq_top_iff, ← B0.span_eq, span_le]
    rintro _ ⟨⟨a, ⟨i, hi⟩⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; exact hy a
    · apply Submodule.mem_sup_right
      rw [cb_isChain_apply N hB0 a (hl a) i hi]
      refine ⟨(N ^ (i - 1)) (B0 ⟨a, ⟨0, hl a⟩⟩), ?_⟩
      rw [cb_pow_succ, show i - 1 + 1 = i by omega]
  have hST : S = ⊤ := cb_eq_top N hN S hS htop
  have hli : LinearIndependent E (cbFam N l y) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [← hSdef, hST])
      (by rw [Module.finrank_eq_card_basis B0])
  refine ⟨Basis.mk hli (by rw [← hSdef, hST]), ?_, fun p => by simp⟩
  exact cb_isChain_of_fam N l y hy0 _ (fun p => by simp)

theorem cb_single (N : W →ₗ[E] W) (L : ℕ) (u : W) (hu : (N ^ L) u = 0) (c : Fin L → E) :
    ∃ s ≤ L, ∃ y : W, (N ^ L) y = 0 ∧ (N ^ s) y = ∑ i, c i • (N ^ (i : ℕ)) u ∧
      u ∈ span E {y} ⊔ LinearMap.range N := by
  classical
  by_cases h : ∃ i, ∃ hi : i < L, c ⟨i, hi⟩ ≠ 0
  · obtain ⟨s, ⟨hsL, hcs⟩, hmin⟩ : ∃ s, (∃ hi : s < L, c ⟨s, hi⟩ ≠ 0) ∧
        ∀ i < s, ∀ hi : i < L, c ⟨i, hi⟩ = 0 :=
      ⟨Nat.find h, Nat.find_spec h, fun i hi hiL => by
        by_contra hne; exact Nat.find_min h hi ⟨hiL, hne⟩⟩
    set y : W := ∑ i : Fin L, if s ≤ (i : ℕ) then c i • (N ^ ((i : ℕ) - s)) u else 0 with hydef
    set z : W := ∑ i : Fin L, if s < (i : ℕ) then c i • (N ^ ((i : ℕ) - s - 1)) u else 0 with hzdef
    refine ⟨s, hsL.le, y, ?_, ?_, ?_⟩
    · rw [hydef, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs
      · rw [map_smul, cb_pow_pow, cb_pow_zero_of_le N hu (by omega), smul_zero]
      · exact map_zero _
    · rw [hydef, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h1
      · rw [map_smul, cb_pow_pow, show s + ((i : ℕ) - s) = i by omega]
      · rw [map_zero, hmin i (by omega) i.2, zero_smul]
    · have hyz : y = c ⟨s, hsL⟩ • u + N z := by
        have hc : c ⟨s, hsL⟩ • u = ∑ i : Fin L, if i = ⟨s, hsL⟩ then c i • u else 0 := by
          rw [Finset.sum_ite_eq']; simp
        rw [hc, hydef, hzdef, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases lt_trichotomy (i : ℕ) s with h1 | h1 | h1
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_neg (by omega), if_neg hne, if_neg (by omega), map_zero, add_zero]
        · have he : i = ⟨s, hsL⟩ := Fin.ext h1
          rw [if_pos (by omega), if_pos he, if_neg (by omega), map_zero, add_zero, h1, Nat.sub_self,
            pow_zero, Module.End.one_apply]
        · have hne : i ≠ ⟨s, hsL⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
          rw [if_pos (by omega), if_neg hne, if_pos h1, zero_add, map_smul, cb_pow_succ,
            show (i : ℕ) - s - 1 + 1 = (i : ℕ) - s by omega]
      have hu_eq : u = (c ⟨s, hsL⟩)⁻¹ • y - N ((c ⟨s, hsL⟩)⁻¹ • z) := by
        rw [hyz, smul_add, smul_smul, inv_mul_cancel₀ hcs, one_smul, map_smul]; abel
      rw [hu_eq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self y))) (Submodule.mem_sup_right (LinearMap.mem_range_self N _))
  · push Not at h
    refine ⟨L, le_rfl, u, hu, ?_, Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)⟩
    rw [hu]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show c i = 0 from h i i.2, zero_smul]

theorem cb_init (N : W →ₗ[E] W) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (v : W) :
    ∃ (y : ι → W) (s : ι → ℕ), (∀ a, (N ^ l a) (y a) = 0) ∧
      (∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) ∧
      (∀ a, s a ≤ l a) ∧ v = ∑ a, (N ^ s a) (y a) := by
  have H : ∀ a, ∃ s ≤ l a, ∃ y : W, (N ^ l a) y = 0 ∧
      (N ^ s) y = ∑ i : Fin (l a), B0.repr v ⟨a, i⟩ • (N ^ (i : ℕ)) (B0 ⟨a, ⟨0, hl a⟩⟩) ∧
      B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E {y} ⊔ LinearMap.range N :=
    fun a => cb_single N (l a) _ (cb_isChain_len N hB0 a (hl a)) _
  choose s hs y hy0 hys hyu using H
  refine ⟨y, s, hy0, fun a => ?_, hs, ?_⟩
  · have hle : span E {y a} ≤ span E (Set.range (cbFam N l y)) := by
      rw [span_le, Set.singleton_subset_iff]
      exact subset_span ⟨⟨a, ⟨0, hl a⟩⟩, by simp [cbFam]⟩
    exact sup_le_sup_right hle _ (hyu a)
  · conv_lhs => rw [← B0.sum_repr v]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hys]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cb_isChain_apply' N hB0 a (hl a) i]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
