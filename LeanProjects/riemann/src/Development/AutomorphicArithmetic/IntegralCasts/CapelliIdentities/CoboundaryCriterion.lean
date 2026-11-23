import Mathlib

theorem UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime :
    ∀ {R G M : Type} [inst : CommRing R]
    [inst_1 : Group G] [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (ρ : Representation R G M) {l : ℕ}
    {H C : Type} [inst_4 : Group H] [inst_5 : Group C] [Finite C] (i : H →* G) (f : H →* C),
    (Nat.card C).Coprime l →
      (∀ (m : M), l • m = (0 : M)) →
        ∀ (z : G → M),
          (∀ (g h : G), z (g * h) = z g + ((ρ : G → M →ₗ[R] M) g : M → M) (z h)) →
            (∀ (u : H), (f : H → C) u = (1 : C) → z ((i : H → G) u) = (0 : M)) →
              ∃ (b : M), ∀ (u : H), z ((i : H → G) u) = ((ρ : G → M →ₗ[R] M) ((i : H → G) u) : M → M) b - b := by
  intro R G M _ _ _ _ ρ l H C _ _ _ i f hcop hl z hz hker
  classical
  have hfac : ∀ u v : H, f u = f v → z (i u) = z (i v) := by
    intro u v huv
    have h1 : z (i (v⁻¹ * u)) = 0 := hker _ (by simp [huv])
    have h2 : i u = i v * i (v⁻¹ * u) := by simp
    rw [h2, hz, h1, map_zero, add_zero]
  haveI : Fintype f.range := Fintype.ofFinite _
  obtain ⟨s, hs⟩ : ∃ s : f.range → H, ∀ q, f (s q) = (q : C) :=
    ⟨fun q => q.2.choose, fun q => q.2.choose_spec⟩
  have hcop' : (Nat.card f.range).Coprime l :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card f.range) hcop
  set n := Nat.card f.range with hn
  set S : M := ∑ q : f.range, z (i (s q)) with hS
  have key : ∀ u : H, S = n • z (i u) + ρ (i u) S := by
    intro u
    have h1 : S = ∑ q : f.range, z (i (s (f.rangeRestrict u * q))) :=
      (Equiv.sum_comp (Equiv.mulLeft (f.rangeRestrict u)) (fun q => z (i (s q)))).symm
    have h2 : ∀ q : f.range,
        z (i (s (f.rangeRestrict u * q))) = z (i u) + ρ (i u) (z (i (s q))) := by
      intro q
      rw [← hz, ← map_mul]
      apply hfac
      simp [hs]
    calc S = ∑ q : f.range, (z (i u) + ρ (i u) (z (i (s q)))) := by
          rw [h1]; exact Finset.sum_congr rfl fun q _ => h2 q
      _ = n • z (i u) + ρ (i u) S := by
          rw [Finset.sum_add_distrib, Finset.sum_const, hS, map_sum, hn, Nat.card_eq_fintype_card,
            Finset.card_univ]
  obtain ⟨a, c, hac⟩ : IsCoprime (n : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop'
  refine ⟨-(a • S), fun u => ?_⟩
  have h3 : (n : ℤ) • z (i u) = S - ρ (i u) S := by
    rw [natCast_zsmul, eq_sub_iff_add_eq]; exact (key u).symm
  have h4 : (l : ℤ) • z (i u) = 0 := by rw [natCast_zsmul, hl]
  calc z (i u) = (a * n + c * l) • z (i u) := by rw [hac, one_smul]
    _ = a • (S - ρ (i u) S) := by rw [add_smul, mul_smul, mul_smul, h3, h4, smul_zero, add_zero]
    _ = ρ (i u) (-(a • S)) - -(a • S) := by
        rw [map_neg, map_zsmul, smul_sub]; abel
