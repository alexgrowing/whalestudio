import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.FixMlIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompactTorusUnitsEqTopOfNonsplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EvenValuationNormCompactUnitsOfSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FinsumQuotientNormsOfNonsplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDiscriminantNormalForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardQuotientSpanUniformizerPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.StabilizerOrderLevelAntitoneLeUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerOrderLevelZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerSuccEqCardResidueField
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerLevelOneOfIsSquareUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSquareSqSubFourIffIsSquareUnit

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem sum_split (I : ℕ → ℕ) (q : ℕ) (h0 : I 0 = 1) (h1 : I 1 + 1 = q)
    (hs : ∀ m, 1 ≤ m → I (m + 1) = q * I m) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), I m = q ^ n := by
  have key : ∀ k, I (k + 1) + q ^ k = q ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [hs (k + 1) (by omega)]
      calc q * I (k + 1) + q ^ (k + 1) = q * (I (k + 1) + q ^ k) := by ring
        _ = q ^ (k + 1 + 1) := by rw [ih]; ring
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    linarith [key k]

private theorem sum_inert (I : ℕ → ℕ) (q : ℕ) (h0 : I 0 = 1) (h1 : I 1 = q + 1)
    (hs : ∀ m, 1 ≤ m → I (m + 1) = q * I m) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + m) * (I m : ℤ) = (q : ℤ) ^ n := by
  have key : ∀ k, (I (k + 1) : ℤ) = (q : ℤ) ^ (k + 1) + (q : ℤ) ^ k := by
    intro k
    induction k with
    | zero => simp [h1]
    | succ k ih =>
      rw [hs (k + 1) (by omega)]
      push_cast
      rw [ih]
      ring
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ m ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + 1 + m) * (I m : ℤ)
        = -∑ m ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + m) * (I m : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [show k + 1 + m = (k + m) + 1 by omega, pow_succ]
      ring
    rw [e, ih, key k, show k + 1 + (k + 1) = 2 * (k + 1) by omega, pow_mul]
    norm_num

section
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}

private theorem ev_odd (L : IsLoc O Δ) {g y : K} (hg0 : g ≠ 0) (hg : ¬ EvenVal O g) (hy : y ≠ 0) :
    EvenVal O (y * g) ↔ ¬ EvenVal O y := by
  constructor
  · intro h hy'
    apply hg
    have e := PS.even_mul h (PS.even_inv hy')
    rwa [show y * g * y⁻¹ = g by field_simp] at e
  · intro hy'
    have h1 := (PS.even_or L hy hg0 hg).resolve_left hy'
    have h2 : EvenVal O (g ^ 2) := ⟨1, g, hg0, by simp⟩
    have e := PS.even_mul h1 h2
    rwa [show y / g * g ^ 2 = y * g by field_simp] at e

private theorem ev_pow (L : IsLoc O Δ) {π : O} (hπ : Irreducible π) (k : ℕ) :
    EvenVal O (algebraMap O K (π ^ k)) ↔ Even k := by
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hπ0 : algebraMap O K π ≠ 0 := by
    intro h
    exact hπ.ne_zero (hinj (by rw [h, map_zero]))
  induction k with
  | zero =>
    simp only [pow_zero, map_one]
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => ⟨1, 1, one_ne_zero, by simp⟩⟩
  | succ k ih =>
    have hy : algebraMap O K (π ^ k) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero k hπ0
    rw [pow_succ, map_mul, ev_odd L hπ0 (PS.not_even_irr L hπ) hy, Nat.even_add_one]
    exact not_congr ih

end

theorem UpperTheory.V.Z.Sym.Loc.pKappa :
    UpperTheory.V.Z.Sym.Loc.PKappa := by
  unfold UpperTheory.V.Z.Sym.Loc.PKappa
  intro O K _ _ _ _ _ Δ τ L hD hτ s ε hDs
  classical
  obtain ⟨π, n, e, h, x, hC, hspan⟩ := UpperTheory.exists_discriminant_normal_form O K Δ τ L hD hτ s ε hDs
  have hπ : Irreducible π := hC.irr
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hπ0 : algebraMap O K π ≠ 0 := by
    intro h0
    exact hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have hodd : ¬ EvenVal O (algebraMap O K π) := PS.not_even_irr L hπ
  have hP : ∀ m, algebraMap O K (π ^ (n + m)) ≠ 0 := fun m => by
    rw [map_pow]
    exact pow_ne_zero _ hπ0
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set r : ℕ → ℕ := fun m => (PK.Hu O (PK.yy π m x)).relIndex (PK.Gu O τ) with hr
  have r0 : r 0 = 1 := UpperTheory.relIndex_stabilizer_order_level_zero O K Δ τ L hD π n e h x hC
  have rs : ∀ m, 1 ≤ m → r (m + 1) = q * r m := by
    intro m hm
    have h1 := (UpperTheory.stabilizer_order_level_antitone_le_units O K Δ τ L hD π n e h x hC m).1
    have h2 := (UpperTheory.stabilizer_order_level_antitone_le_units O K Δ τ L hD π n e h x hC m).2
    simp only [hr]
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2, UpperTheory.relIndex_stabilizer_succ_eq_card_residueField O K Δ τ L hD π n e h x hC m hm]
  have hcount : ∀ t : Kˣ, ((PS.Gs O τ (↑t) 1).ncard : ℂ) = ∑ m ∈ Finset.range (n + 1),
      if EvenVal O ((t : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0 := by
    intro t
    rw [PK.gs_count L hD hC t]
    push_cast
    rfl
  have hRHS : Nat.card (O ⧸ Ideal.span {s}) = q ^ n := by
    rw [hspan, UpperTheory.card_quotient_span_uniformizer_pow O K Δ τ L π hπ n]
  rw [hRHS]
  have hDe := UpperTheory.isSquare_sq_sub_four_iff_isSquare_unit O K Δ τ L hD π n e h x hC
  have hL := hsLaw O K Δ L
  by_cases hsq : IsSquare (τ ^ 2 - 4)
  · have hE : IsSquare (e : O) := hDe.1 hsq
    have r1 : r 1 + 1 = q := (UpperTheory.relIndex_stabilizer_level_one_of_isSquare_unit O K Δ τ L hD π n e h x hC).2 hE
    have hall : ∀ t : Kˣ, t ∈ NE τ := fun t => (hsNE O K Δ τ L hD t).2 (hL.2.2.2 _ _ hD hsq)
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 (hall (Units.mk0 (algebraMap O K π) hπ0))
    have hnb' : PS.nU b = Units.mk0 (algebraMap O K π) hπ0 := hb
    have hnb : QuadraticAlgebra.norm (b : Etau K τ) = algebraMap O K π := by
      rw [← PS.nU_val, hnb', Units.val_mk0]
    have hC13 := UpperTheory.evenValuation_norm_compactUnits_of_split O K Δ τ L hD hsq
    have hbC : b ∉ Cint O τ := by
      intro hb'
      have := hC13.1 b hb'
      rw [hnb] at this
      exact hodd this
    have cover : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = b * c * z ^ 2 := by
      intro y
      have hy0 : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := by
        rw [← PS.nU_val]
        exact Units.ne_zero _
      rcases PS.even_or L hy0 hπ0 hodd with hev | hev
      · obtain ⟨z, c, hc, hyz⟩ := hC13.2 y hev
        exact ⟨z, c, hc, Or.inl (by rw [hyz, one_mul])⟩
      · have hev' : EvenVal O (QuadraticAlgebra.norm ((b⁻¹ * y : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [← PS.nU_val]
          simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, PS.nU_val, hnb]
          rwa [div_eq_mul_inv, mul_comm] at hev
        obtain ⟨z, c, hc, hyz⟩ := hC13.2 _ hev'
        exact ⟨z, c, hc, Or.inr (by rw [mul_assoc, ← hyz, mul_inv_cancel_left])⟩
    have uniq : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * b⁻¹ ∈ Cint O τ → z ∈ Cint O τ := by
      intro z hz
      exfalso
      apply hodd
      have h1 : EvenVal O (QuadraticAlgebra.norm ((z ^ 2 * 1 * b⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := hC13.1 _ hz
      have h2 : EvenVal O (((PS.nU z : Kˣ) : K) ^ 2) := ⟨1, _, Units.ne_zero _, by rw [Units.val_one, map_one, one_mul]⟩
      have h3 := PS.even_mul h2 (PS.even_inv h1)
      have e3 : ((PS.nU z : Kˣ) : K) ^ 2 * (QuadraticAlgebra.norm ((z ^ 2 * 1 * b⁻¹ : (Etau K τ)ˣ) : Etau K τ))⁻¹
          = algebraMap O K π := by
        rw [← PS.nU_val, ← hnb, ← PS.nU_val]
        simp only [map_mul, map_pow, map_one, mul_one, map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
          Units.val_inv_eq_inv_val]
        field_simp
      rwa [e3] at h3
    have disj : ∀ t : K, Disjoint (PS.Gs O τ t 1) (PS.Gs O τ t b) := by
      intro t
      rw [Set.disjoint_left]
      rintro S ⟨_, c, hc, hg⟩ ⟨_, c', hc', hg'⟩
      have hu := PS.gen_uniq hg hg'
      apply hbC
      have e1 : b = (1 * c) * ((1 * c)⁻¹ * (b * c')) * c'⁻¹ := by group
      rw [e1]
      exact (Cint O τ).mul_mem ((Cint O τ).mul_mem (by rwa [one_mul]) hu) ((Cint O τ).inv_mem hc')
    have hp : ∀ t : Kˣ, pcount O τ (t : K) = ((PS.Gs O τ (↑t) 1).ncard : ℂ)
        + ((PS.Gs O τ (↑(t * Units.mk0 (algebraMap O K π) hπ0)) 1).ncard : ℂ) := by
      intro t
      rw [PS.pcount_eq L hD t 1 b cover uniq,
        Set.ncard_union_eq (disj _) (PS.gs_fin L hD t 1) (PS.gs_fin L hD t b), PS.gs_ncard (↑t) b, hnb',
        ← Units.val_mul]
      exact Nat.cast_add _ _
    haveI : Unique (Kˣ ⧸ NE τ) :=
      { default := 1
        uniq := fun u => by
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
          exact (QuotientGroup.eq_one_iff a).2 (hall a) }
    rw [finsum_unique]
    have hterm : ∀ t0 : Kˣ, ∀ m ∈ Finset.range (n + 1),
        ((if EvenVal O ((t0 : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0) +
          (if EvenVal O (((t0 * Units.mk0 (algebraMap O K π) hπ0 : Kˣ) : K) * algebraMap O K (π ^ (n + m)))
            then (r m : ℂ) else 0)) = (r m : ℂ) := by
      intro t0 m _
      rw [Units.val_mul, Units.val_mk0,
        show (t0 : K) * algebraMap O K π * algebraMap O K (π ^ (n + m))
          = (t0 : K) * algebraMap O K (π ^ (n + m)) * algebraMap O K π by ring,
        ev_odd L hπ0 hodd (mul_ne_zero (Units.ne_zero t0) (hP m))]
      by_cases hE : EvenVal O ((t0 : K) * algebraMap O K (π ^ (n + m)))
      · rw [if_pos hE, if_neg (not_not.2 hE), add_zero]
      · rw [if_neg hE, if_pos hE, zero_add]
    rw [hL.2.2.2 _ _ hD hsq, one_mul, hp, hcount, hcount, ← Finset.sum_add_distrib, Finset.sum_congr rfl (hterm _)]
    exact_mod_cast sum_split r q r0 r1 rs n
  · have hE : ¬ IsSquare (e : O) := fun h' => hsq (hDe.2 h')
    have r1 : r 1 = q + 1 := (UpperTheory.relIndex_stabilizer_level_one_of_isSquare_unit O K Δ τ L hD π n e h x hC).1 hE
    have hCt : Cint O τ = ⊤ := UpperTheory.compactTorusUnits_eq_top_of_nonsplit O K Δ τ L hD hsq
    obtain ⟨⟨g, hg⟩, hfin⟩ := UpperTheory.finsum_quotient_norms_of_nonsplit O K Δ τ L hD hsq
    have cover : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = 1 * c * z ^ 2 :=
      fun y => ⟨1, y, by rw [hCt]; exact Subgroup.mem_top _, Or.inl (by simp)⟩
    have uniq : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * 1⁻¹ ∈ Cint O τ → z ∈ Cint O τ :=
      fun z _ => by rw [hCt]; exact Subgroup.mem_top _
    have hp : ∀ t : Kˣ, pcount O τ (t : K) = ((PS.Gs O τ (↑t) 1).ncard : ℂ) := by
      intro t
      rw [PS.pcount_eq L hD t 1 1 cover uniq, Set.union_self]
    have hGs : ∀ (t : K) (a : (Etau K τ)ˣ), PS.Gs O τ t a = PS.Gs O τ t 1 := by
      intro t a
      ext S
      simp only [PS.Gs, Set.mem_setOf_eq, hCt, Subgroup.mem_top, true_and, one_mul]
      constructor
      · rintro ⟨hf, c, hc⟩
        exact ⟨hf, a * c, hc⟩
      · rintro ⟨hf, c, hc⟩
        exact ⟨hf, a⁻¹ * c, by rwa [mul_inv_cancel_left]⟩
    have hs0 : algebraMap O K s ≠ 0 := by
      intro h0
      apply hD
      rw [hDs, map_mul, map_pow, h0]
      ring
    have hDv : EvenVal O (τ ^ 2 - 4) := ⟨ε, algebraMap O K s, hs0, by rw [hDs, map_mul, map_pow]⟩
    have hg1 : hs (τ ^ 2 - 4) (g : K) = -1 := by
      have h1 : ¬ hs (τ ^ 2 - 4) (g : K) = 1 := fun h' => hg ((hsNE O K Δ τ L hD g).2 h')
      unfold UpperTheory.V.Z.Sym.Loc.hs at h1 ⊢
      split_ifs at h1 ⊢
      · exact absurd rfl h1
      · rfl
    have hgodd : ¬ EvenVal O (g : K) := fun hev => by
      have h2 := hL.2.1 _ _ hDv hev
      rw [hg1] at h2
      norm_num at h2
    have hinv : ∀ t ∈ NE τ, ∀ y : Kˣ, hs (τ ^ 2 - 4) ((t * y : Kˣ) : K) * pcount O τ ((t * y : Kˣ) : K)
        = hs (τ ^ 2 - 4) (y : K) * pcount O τ (y : K) := by
      intro t ht y
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 ht
      have ha' : PS.nU a = t := ha
      rw [Units.val_mul, hsMul O K Δ L _ _ _ hD (Units.ne_zero _) (Units.ne_zero _),
        (hsNE O K Δ τ L hD t).1 ht, one_mul, ← Units.val_mul, hp, hp]
      congr 1
      rw [Units.val_mul, mul_comm, ← ha', ← PS.gs_ncard, hGs]
    have hf := hfin (fun t : Kˣ => hs (τ ^ 2 - 4) (t : K) * pcount O τ (t : K)) hinv g hg
    rw [hf]
    have hterm : ∀ m ∈ Finset.range (n + 1),
        ((if EvenVal O (((1 : Kˣ) : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0) +
          -(if EvenVal O ((g : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0))
          = (-1 : ℂ) ^ (n + m) * (r m : ℂ) := by
      intro m _
      rw [Units.val_one, one_mul, ev_pow L hπ, mul_comm (g : K),
        ev_odd L (Units.ne_zero g) hgodd (hP m), ev_pow L hπ]
      by_cases hev : Even (n + m)
      · simp [hev, hev.neg_one_pow]
      · simp [hev, (Nat.not_even_iff_odd.1 hev).neg_one_pow]
    rw [(hsNE O K Δ τ L hD 1).1 (NE τ).one_mem, hg1, hp, hp, hcount, hcount, one_mul, neg_one_mul,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm]
    exact_mod_cast sum_inert r q r0 r1 rs n
