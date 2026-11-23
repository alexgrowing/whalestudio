import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AbEval

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_prime_power_pow_eq_one {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] [IsLocalRing D]
    [CharP D l] {x : D} (hx : x - 1 ∈ maximalIdeal D) {h : ℕ} (hh : h ≠ 0) (hp : x ^ h = 1) : x = 1 := by
  have hl : l.Prime := Fact.out
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hl.ne_one
  have h1 : (x ^ m - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hp, sub_self]
  have h2 : x ^ m - 1 = 0 := (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1
  rw [← mul_geom_sum, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact sub_eq_zero.1 h2
  · exfalso
    have h3 : residue D x = 1 := by
      have := (residue_eq_zero_iff _).2 hx
      rwa [map_sub, map_one, sub_eq_zero] at this
    have h4 := congrArg (residue D) h2
    simp only [map_sum, map_pow, h3, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      map_zero] at h4
    have h5 : (l : ResidueField D) = 0 := by
      rw [← map_natCast (residue D), CharP.cast_eq_zero, map_zero]
    haveI : CharP (ResidueField D) l := (CharP.charP_iff_prime_eq_zero hl).2 h5
    exact hm ((CharP.cast_eq_zero_iff _ l m).1 h4)

theorem UpperTheory.V.Fr.frobenius_corner_middle_trivial :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [IsCO O D], (∀ c ∈ maximalIdeal O, algebraMap O D c = 0) → ∀ χ : F.G0 →* D, AdicCont (maximalIdeal D) χ → (∀ g, χ g - 1 ∈ maximalIdeal D) → (∀ g, χ (F.star g) = χ g) → (∀ v g, g ∈ F.Iv v → F.Ψ (F.loc v g) = 1 → χ (F.loc0 v g) = 1) → ∀ g, χ g = 1 := by
  intro l _ O _ _ _ _ F C₀ hF D _ _ _ _ hO χ hc h1 hs hI g
  have hl : l.Prime := Fact.out
  have hlO : (l : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  haveI : CharP D l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (algebraMap O D), hO _ hlO])
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ hF.del_open).isCompact
  obtain ⟨s, s', h, hh, -, hs', H⟩ := UpperTheory.V.Fr.ab_gen hF
  refine exists_prime_power_pow_eq_one (h1 g) hh ?_
  have key : ∀ N : ℕ, χ g ^ h - 1 ∈ maximalIdeal D ^ N := by
    intro N
    let q := Ideal.Quotient.mk (maximalIdeal D ^ N)
    let φ : F.G0 →* (D ⧸ maximalIdeal D ^ N)ˣ := ((q : D →* _).comp χ).toHomUnits
    have hφ : ∀ x, (φ x : D ⧸ maximalIdeal D ^ N) = q (χ x) := fun _ => rfl
    have hone : ∀ x n, φ.rangeRestrict x ^ n = 1 ↔ χ x ^ n - 1 ∈ maximalIdeal D ^ N := by
      intro x n
      rw [← Ideal.Quotient.eq, Subtype.ext_iff, Units.ext_iff, map_pow, map_one]
      rfl
    haveI : Finite φ.range := by
      haveI hf : Finite (Set.range fun g => q (χ g)) := (hc N).range_finite
      refine Finite.of_injective (β := Set.range fun g => q (χ g))
        (fun y => ⟨(y.1 : D ⧸ maximalIdeal D ^ N), ?_⟩) ?_
      · obtain ⟨_, x, rfl⟩ := y
        exact ⟨x, rfl⟩
      · intro y z hyz
        exact Subtype.ext (Units.ext (congrArg Subtype.val hyz))
    have hP : IsPGroup l φ.range := by
      intro y
      obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective y
      refine ⟨N, (hone x _).2 ?_⟩
      have e : χ x ^ l ^ N - 1 = (χ x - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
      rw [e]
      exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl.one_lt).le (Ideal.pow_mem_pow (h1 x) _)
    have hop : IsOpen (φ.rangeRestrict.ker : Set F.G0) := by
      convert (hc N).isOpen_fiber 1 using 1
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [Subtype.ext_iff, Units.ext_iff]
      rfl
    refine (hone g h).1 ((H φ.range hP φ.rangeRestrict hop).2 (fun x => ?_) (fun a => ?_) g)
    · refine Subtype.ext (Units.ext ?_)
      show q (χ _) = q (χ _)
      rw [hs]
    · obtain ⟨v, x, hx, hΨ, e⟩ := hs' a
      refine Subtype.ext (Units.ext ?_)
      show q (χ _) = 1
      rw [e, hI v x hx hΨ, map_one]
  rw [← sub_eq_zero]
  have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal D) (maximalIdeal.isMaximal D).ne_top
  rw [← Ideal.mem_bot, ← hb]
  exact Ideal.mem_iInf.2 key
