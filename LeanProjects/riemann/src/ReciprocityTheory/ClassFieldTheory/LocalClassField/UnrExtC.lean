import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Polynomial

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem finiteDimensional_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    FiniteDimensional ℚ_[p] (Kn p K n) := by
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : 0 < qK p K ^ n - 1 := Nat.pos_of_ne_zero (by rintro h; exact hnd (h ▸ dvd_zero p))
  have hfin : Finite {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} := by
    have : {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} =
        (nthRootsFinset (qK p K ^ n - 1) (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
      ext ζ
      simp [mem_nthRootsFinset hm0]
    rw [this]
    exact Finset.finite_toSet _
  have h2 : FiniteDimensional ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact IntermediateField.finiteDimensional_sup _ _

theorem extendScalars_Kn_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (qK p K ^ n - 1))
    (hm : qK p K ^ n - 1 ≠ 0) :
    IntermediateField.extendScalars (le_Kn p K n) = IntermediateField.adjoin K {ζ} := by
  apply le_antisymm
  · have h : Kn p K n ≤ (IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[p] := by
      apply UnramifiedExtensions.Kn_le
      · intro y hy
        exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨y, hy⟩
      · intro ξ hξ
        have : NeZero (qK p K ^ n - 1) := ⟨hm⟩
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
        exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) i
    exact h
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact mem_Kn_of_pow p K hζ.pow_eq_one

theorem natDegree_minpoly_le (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K ^ n - 1) = 1) : (minpoly K ζ).natDegree ≤ n := by
  classical
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hsep : (minpoly K ζ).Separable := (minpoly.irreducible hint).separable
  have hcard := card_rootSet_eq_natDegree (K := PadicAlgCl p) hsep (IsAlgClosed.splits _)
  calc (minpoly K ζ).natDegree = Fintype.card ((minpoly K ζ).rootSet (PadicAlgCl p)) := hcard.symm
    _ = ((minpoly K ζ).rootSet (PadicAlgCl p)).toFinset.card := (Set.toFinset_card _).symm
    _ ≤ ((Finset.range n).image (fun i => ζ ^ (qK p K ^ i))).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Set.mem_toFinset] at hy
        obtain ⟨σ, hσ⟩ := ((isConjRoot_iff_mem_minpoly_rootSet hint).2 hy).symm.exists_algEquiv
        obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, by rw [← h, hσ]⟩
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

theorem finrank_unramified_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n ∧ qK p (Kn p K n) = qK p K ^ n := by
  have hq := one_lt_qK p K hK
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : qK p K ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hfd := finiteDimensional_Kn p K hK hn
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hup : Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) ≤ n := by
    rw [extendScalars_Kn_eq_adjoin p K hζ hm0, IntermediateField.adjoin.finrank hint]
    exact natDegree_minpoly_le p K hK hn hζ.pow_eq_one
  obtain ⟨f, hf, hqf, hle⟩ := qK_le_pow_finrank p K hK hfd (le_Kn p K n)
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n)] at hmul
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ.pow_eq_one

  have hnf : n ≤ f := by
    have hmem : UnramifiedExtensions.red ζ ∈ resK p (Kn p K n) :=
      (UnramifiedExtensions.mem_resK_iff _ _).2 ⟨⟨ζ, mem_Obar_iff.2 h1.le⟩, mem_Kn_of_pow p K hζ.pow_eq_one,
        (UnramifiedExtensions.red_of_le h1.le).symm⟩
    have h2 := UnramifiedExtensions.pow_qK_eq (Kn p K n) hfd hmem
    rw [hqf, ← UnramifiedExtensions.red_pow h1.le] at h2
    have hζf : (ζ ^ (qK p K ^ f)) ^ (qK p K ^ n - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h3 : ζ ^ (qK p K ^ f) = ζ := by
      by_contra hne
      have h4 := UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hnd hζf hζ.pow_eq_one hne
      have h5 := (UnramifiedExtensions.red_eq_iff (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζf).le h1.le).1 h2
      exact absurd h4 (ne_of_lt h5)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [norm_zero] at h1; exact zero_ne_one h1
    have hf1 : 1 ≤ qK p K ^ f := Nat.one_le_pow _ _ (by omega)
    have h6 : ζ ^ (qK p K ^ f - 1) = 1 := by
      have h7 : qK p K ^ f = (qK p K ^ f - 1) + 1 := by omega
      rw [h7, pow_succ] at h3
      exact mul_right_cancel₀ hζ0 (by rw [h3, one_mul])
    have h8 := (hζ.pow_eq_one_iff_dvd _).1 h6
    have h9 : 1 < qK p K ^ f := Nat.one_lt_pow hf.ne' hq
    have h10 := Nat.le_of_dvd (by omega) h8
    have h11 : qK p K ^ n ≤ qK p K ^ f := by
      have : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).1 h11
  have hkey : f * Module.finrank ℚ_[p] K ≤
      Module.finrank ℚ_[p] K * Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [hmul]; exact hle
  have hfle : f ≤ Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [mul_comm] at hkey
    exact Nat.le_of_mul_le_mul_left hkey hd
  have hfn : f = n := by omega
  exact ⟨by omega, by rw [hqf, hfn]⟩

theorem finrank_extendScalars_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n :=
  (finrank_unramified_extension p K hK hn).1

theorem finrank_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ_[p] (Kn p K n) = n * Module.finrank ℚ_[p] K := by
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n), finrank_extendScalars_Kn p K hK hn] at hmul
  rw [← hmul, mul_comm]

theorem qK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    qK p (Kn p K n) = qK p K ^ n :=
  (finrank_unramified_extension p K hK hn).2

theorem norm_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : ∃ y ∈ K, ‖x‖ = ‖y‖ :=
  exists_norm_eq_of_qK p K hK (le_Kn p K n) hn (finrank_Kn p K hK hn) (qK_Kn p K hK hn) hx

theorem isGalois_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsGalois K (IntermediateField.extendScalars (le_Kn p K n)) := by
  have hnorm : Normal K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact map_mem_Kn p K n σ hx
  exact ⟨⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
