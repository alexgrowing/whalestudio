import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.okFin :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → (∀ k, Finite (Ok l O k)) ∧ (∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c})) ∧ (∀ k, (∀ x : Ok l O k, l ^ k • x = 0)) ∧ (∀ k, 2 ^ k ≤ Nat.card (Ok l O k)) ∧ (∀ k, ∃ N, maximalIdeal O ^ N ≤ Ideal.span {(l : O) ^ k}) ∧ (∀ k (a : ℤ_[l]) (x : Ok l O k), algebraMap ℤ_[l] O a • x = (PadicInt.toZModPow k a).val • x) ∧ (∀ k, 0 < k → Ideal.span {(l : O) ^ k} ≤ maximalIdeal O) := by
  intro l _ O _ _ _ _ _ hl
  haveI hchar := IsCoef.char (l := l) (O := O)
  haveI hfinres := IsCoef.fin (l := l) (O := O)
  have hlm : (l : O) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hlu : ¬ IsUnit (l : O) := fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hlm) hu
  have hfinc : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}) := by
    intro c hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    apply IsLocalRing.finite_quotient_iff.mpr
    refine ⟨n, ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact Units.mul_left_dvd.mpr dvd_rfl
  have hfin : ∀ k, Finite (Ok l O k) := fun k => hfinc _ (pow_ne_zero k hl)
  have hcard : ∀ k, 2 ^ k ≤ Nat.card (Ok l O k) := by
    intro k
    induction k with
    | zero =>
      haveI := hfin 0
      rw [pow_zero]
      exact Nat.card_pos
    | succ k ih =>
      haveI := hfin k
      haveI := hfin (k + 1)
      have hle : Ideal.span {(l : O) ^ (k + 1)} ≤ Ideal.span {(l : O) ^ k} := by
        rw [Ideal.span_singleton_le_span_singleton]
        exact pow_dvd_pow _ (Nat.le_succ k)
      let g : Ok l O (k + 1) →+ Ok l O k := (Ideal.Quotient.factor hle).toAddMonoidHom
      have hsurj : Function.Surjective g := Ideal.Quotient.factor_surjective hle
      have hmem : Ideal.Quotient.mk (Ideal.span {(l : O) ^ (k + 1)}) ((l : O) ^ k) ∈ g.ker := by
        rw [AddMonoidHom.mem_ker]
        show Ideal.Quotient.factor hle (Ideal.Quotient.mk _ ((l : O) ^ k)) = 0
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      have hne : Ideal.Quotient.mk (Ideal.span {(l : O) ^ (k + 1)}) ((l : O) ^ k) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_dvd_pow_iff hl hlu]
        omega
      haveI : Nontrivial g.ker := nontrivial_of_ne ⟨_, hmem⟩ 0 (fun h => hne (congrArg Subtype.val h))
      have h2 : 2 ≤ Nat.card g.ker := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have hrange : Nat.card g.range = Nat.card (Ok l O k) := by
        rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top]
      calc 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        _ ≤ Nat.card (Ok l O k) * Nat.card g.ker := Nat.mul_le_mul ih h2
        _ = Nat.card g.ker * g.ker.index := by rw [AddSubgroup.index_ker, hrange, mul_comm]
        _ = Nat.card (Ok l O (k + 1)) := AddSubgroup.card_mul_index _
  refine ⟨hfin, hfinc, ?_, hcard, ?_, ?_, ?_⟩
  · intro k x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro k
    haveI := hfin k
    exact IsLocalRing.finite_quotient_iff.mp (hfin k)
  · intro k a x
    have hmem : a - (((PadicInt.toZModPow k a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) k) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨b, hb⟩ := hmem
    have ha : algebraMap ℤ_[l] O a =
        (((PadicInt.toZModPow k a).val : ℕ) : O) + algebraMap ℤ_[l] O b * (l : O) ^ k := by
      have h0 := congrArg (algebraMap ℤ_[l] O) hb
      simp only [map_mul, map_sub, map_pow, map_natCast] at h0
      linear_combination (-1 : O) * h0
    have hz : (algebraMap ℤ_[l] O b * (l : O) ^ k) • x = 0 := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [ha, add_smul, Nat.cast_smul_eq_nsmul, hz, add_zero]
  · intro k hk
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_of_mem _ hlm k hk
