import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqNsmulOfForallDvdOfBijective

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_forall_exists_sub_eq_nsmul (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (W : Submodule ℤ Λ) (hW : ∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) (x : Λ)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ W, ∃ b : Λ, x - w = N • b) : x ∈ W := by
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ W) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W m
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hrm
      exact (Submodule.Quotient.mk_eq_zero W).mpr (hW r y hr hrm)
  have hfree : Module.Free ℤ (Λ ⧸ W) := Module.free_iff_isTorsionFree.mpr htf
  let bs := Module.Free.chooseBasis ℤ (Λ ⧸ W)
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine bs.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨w, hw, b, hb⟩ := h ((bs.repr (Submodule.Quotient.mk x) i).natAbs + 1) (by omega)
  generalize hn : (bs.repr (Submodule.Quotient.mk x) i).natAbs = n at hb
  have hq : (Submodule.Quotient.mk x : Λ ⧸ W) = (n + 1) • Submodule.Quotient.mk b := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← hb]
    simpa using hw
  have hc : bs.repr (Submodule.Quotient.mk x) i =
      ((n + 1 : ℕ) : ℤ) * bs.repr (Submodule.Quotient.mk b) i := by
    rw [hq, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  have habs := congrArg Int.natAbs hc
  rw [Int.natAbs_mul, Int.natAbs_natCast, hn] at habs
  rcases Nat.eq_zero_or_pos (bs.repr (Submodule.Quotient.mk b) i).natAbs with ht | ht
  · rw [ht, mul_zero] at habs
    rw [habs] at hn
    exact Int.natAbs_eq_zero.mp hn
  · nlinarith

theorem mem_of_forall_card_mul_eq_pow :
    ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
      (B : LinearMap.BilinForm ℤ Λ), Function.Bijective B → (∀ x, B x x = 0) →
      ∀ W : Submodule ℤ Λ, (∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) →
      (∀ N : ℕ, 0 < N →
        ∃ T : Set (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))),
          Nat.card (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) * Nat.card T
            = N ^ Module.finrank ℤ Λ ∧
          ∀ x y : W, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ B x y) →
      ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ W := by
  intro Λ _ _ _ B hB halt W hW hT x hx
  apply mem_of_forall_exists_sub_eq_nsmul Λ W hW x
  intro N hN
  obtain ⟨T, hcard, hTpair⟩ := hT N hN
  let R : Λ → (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) → Prop :=
    fun a p => ∃ w : W, Submodule.Quotient.mk w = p ∧ ∃ b : Λ, a - w = N • b
  have h1 : ∀ a b p, R a p → R (a + N • b) p := by
    rintro a b p ⟨w, hw, b0, hb0⟩
    refine ⟨w, hw, b0 + b, ?_⟩
    rw [smul_add, ← hb0]
    abel
  have h2 : ∀ a p p', R a p → R a p' → p = p' := by
    rintro a p p' ⟨w, rfl, b, hb⟩ ⟨w', rfl, b', hb'⟩
    have hdiff : ((w : Λ) - w') = (N : ℤ) • (b' - b) := by
      rw [natCast_zsmul, smul_sub, ← hb, ← hb']
      abel
    have hmem : b' - b ∈ W :=
      hW (N : ℤ) (b' - b) (by exact_mod_cast hN.ne') (by rw [← hdiff]; exact W.sub_mem w.2 w'.2)
    rw [Submodule.Quotient.eq]
    refine ⟨⟨b' - b, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hdiff.symm
  have h3 : ∀ p, ∃ a, R a p := by
    intro p
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    exact ⟨w, w, rfl, 0, by simp⟩
  have h4 : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ B a a' := by
    rintro a p a' p' ⟨w, rfl, b, hb⟩ hp ⟨w', -, b', hb'⟩
    have ha : a = w + N • b := by rw [← hb]; abel
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    have hww := hTpair w w' hp
    have hexp : B (↑w + N • b) (↑w' + N • b') = B w w' + N * (B w b' + B b w' + N * B b b') := by
      simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    rw [ha, ha', hexp]
    exact dvd_add hww (dvd_mul_right _ _)
  have h5 : ∀ a' p', R a' p' → (N : ℤ) ∣ B x a' := by
    rintro a' p' ⟨w', -, b', hb'⟩
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    rw [ha', map_add, map_nsmul, hx w' w'.2, zero_add]
    exact ⟨B x b', nsmul_eq_mul _ _⟩
  obtain ⟨p, w, -, b, hwb⟩ :=
    GlobalTheory.exists_rel_of_forall_dvd_of_card_mul Λ B hB N hN _ T R h1 h2 h3 hcard h4 x h5
  exact ⟨w, w.2, b, hwb⟩

end GlobalTheory.CompanionTheory.Ar.Flat
