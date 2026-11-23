import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.BridgeDefs
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Duality

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private lemma filt_gcd_eq {t : ℕ} (ht : t ≤ N.factorization l) :
    Nat.gcd N (ordCompl[l] N * l ^ t) = ordCompl[l] N * l ^ t := by
  apply Nat.gcd_eq_right
  calc ordCompl[l] N * l ^ t ∣ ordCompl[l] N * l ^ N.factorization l :=
        Nat.mul_dvd_mul_left _ (pow_dvd_pow _ ht)
    _ = N := by rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self N l

private lemma filt_mem_ker_iff {d e : ℕ} (hd : d ∣ N) (he : N = e * d) (g : (ZMod N)ˣ) :
    g ∈ (ZMod.unitsMap hd).ker ↔ addOrderOf ((g : ZMod N) - 1) ∣ e := by
  have he0 : e ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (by simpa using he)
  have h1 : g ∈ (ZMod.unitsMap hd).ker ↔ ZMod.castHom hd (ZMod d) ((g : ZMod N) - 1) = 0 := by
    rw [MonoidHom.mem_ker, Units.ext_iff, map_sub, map_one, sub_eq_zero]
    rfl
  rw [h1, addOrderOf_dvd_iff_nsmul_eq_zero]
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective ((g : ZMod N) - 1)
  rw [← hn, map_natCast, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    ZMod.natCast_eq_zero_iff]
  conv_rhs => rw [he]
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero he0)).symm

private lemma filt_mem_higher {t : ℕ} (ht : t ≤ N.factorization l) (g : (ZMod N)ˣ) :
    g ∈ higherUnits N l t ↔ addOrderOf ((g : ZMod N) - 1) ∣ l ^ (N.factorization l - t) := by
  apply filt_mem_ker_iff
  rw [filt_gcd_eq l ht, mul_left_comm, ← pow_add, Nat.sub_add_cancel ht, mul_comm]
  exact (Nat.ordProj_mul_ordCompl_eq_self N l).symm

private lemma filt_card_ker {d : ℕ} (hd : d ∣ N) :
    Nat.card (ZMod.unitsMap hd).ker * Nat.totient d = Nat.totient N := by
  haveI : NeZero d := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hd⟩
  have h := Subgroup.card_mul_index (ZMod.unitsMap hd).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective hd),
    Subgroup.card_top] at h
  simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using h

private lemma filt_card_higher {t : ℕ} (ht : t ≤ N.factorization l) :
    Nat.card (higherUnits N l t) * Nat.totient (l ^ t) =
      Nat.totient (l ^ N.factorization l) := by
  have hl : l.Prime := Fact.out
  have h := filt_card_ker (Nat.gcd_dvd_left N (ordCompl[l] N * l ^ t))
  have hc : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl (NeZero.ne N)
  have hN : Nat.totient N = Nat.totient (l ^ N.factorization l) * Nat.totient (ordCompl[l] N) := by
    rw [← Nat.totient_mul (hc.pow_left _), Nat.ordProj_mul_ordCompl_eq_self]
  have hpos : 0 < Nat.totient (ordCompl[l] N) :=
    Nat.totient_pos.mpr (Nat.ordCompl_pos l (NeZero.ne N))
  change Nat.card (higherUnits N l t) * _ = _ at h
  rw [filt_gcd_eq l ht, Nat.totient_mul (hc.pow_left t).symm, hN] at h
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h]; ring

private lemma filt_telescope {v k : ℕ} (hk : k < v) :
    ∑ t ∈ Finset.range (k + 1), (Nat.totient (l ^ t) : ℚ) / (Nat.totient (l ^ v) : ℚ) =
      1 / (Nat.totient (l ^ (v - k)) : ℚ) := by
  have hl : l.Prime := Fact.out
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have h1 : ∑ t ∈ Finset.range (k + 1), Nat.totient (l ^ t) = l ^ k := by
    rw [← Nat.sum_divisors_prime_pow hl, Nat.sum_totient]
  rw [h1]
  obtain ⟨j, rfl⟩ : ∃ j, v = k + j + 1 := ⟨v - k - 1, by omega⟩
  have : k + j + 1 - k = j + 1 := by omega
  rw [this, Nat.totient_prime_pow_succ hl, Nat.totient_prime_pow_succ hl]
  have h2 : ((l - 1 : ℕ) : ℚ) ≠ 0 := by
    have := hl.two_le
    exact Nat.cast_ne_zero.mpr (by omega)
  have h3 : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  push_cast
  field_simp
  ring

private lemma filt_mem_ann {t : ℕ} (ht : t ≤ N.factorization l) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) ↔ condExp l ψ ≤ t := by
  have hl : l.Prime := Fact.out
  have h1 : ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) ↔
      ψ.conductor ∣ Nat.gcd N (ordCompl[l] N * l ^ t) := by
    rw [← mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left _ _), mem_conductorSet_iff,
      factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_left _ _), mem_annihilator_iff]
    refine forall_congr' fun a => imp_congr Iff.rfl ?_
    rw [MonoidHom.mem_ker, Units.ext_iff]
    simp
  rw [h1, filt_gcd_eq l ht, condExp]
  have hc := ψ.conductor_ne_zero
  have hN' : ordCompl[l] N ≠ 0 := (Nat.ordCompl_pos l (NeZero.ne N)).ne'
  have hp : l ^ t ≠ 0 := pow_ne_zero _ hl.ne_zero
  constructor
  · intro h
    have := (Nat.factorization_le_iff_dvd hc (mul_ne_zero hN' hp)).mpr h l
    rw [Nat.factorization_mul hN' hp] at this
    simpa [Nat.factorization_ordCompl, hl.factorization_pow] using this
  · intro h
    rw [← Nat.ordProj_mul_ordCompl_eq_self ψ.conductor l, mul_comm]
    exact Nat.mul_dvd_mul (Nat.ordCompl_dvd_ordCompl_of_dvd ψ.conductor_dvd_level l)
      (pow_dvd_pow _ h)

private lemma filt_card_ann (H : Subgroup (ZMod N)ˣ) :
    Nat.card (annihilator ℂ (H : Set (ZMod N)ˣ)) = H.index := by
  have : annihilator ℂ (H : Set (ZMod N)ˣ) =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual := by
    ext ψ
    rw [mem_annihilator_iff, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    rfl
  rw [this, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  rfl

private lemma filt_ann_sup (U H : Subgroup (ZMod N)ˣ) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ annihilator ℂ ((U ⊔ H : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) ↔
      ψ ∈ annihilator ℂ (H : Set (ZMod N)ˣ) ∧ ψ ∈ annihilator ℂ (U : Set (ZMod N)ˣ) := by
  simp only [mem_annihilator_iff, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Subgroup.mem_sup_right ha), fun a ha => h a (Subgroup.mem_sup_left ha)⟩
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp ha
    rw [Units.val_mul, map_mul, h2 x hx, h1 y hy, mul_one]

private lemma filt_index {G : Type*} [CommGroup G] [Finite G] (U H : Subgroup G) :
    ((U ⊔ H).index : ℚ) / (H.index : ℚ) = (Nat.card ↥(U ⊓ H) : ℚ) / (Nat.card U : ℚ) := by
  have h1 : H.relIndex U * (U ⊔ H).index = H.index := by
    rw [← Subgroup.relIndex_sup_right U H]
    exact Subgroup.relIndex_mul_index le_sup_right
  have h2 : H.relIndex U * Nat.card ↥(U ⊓ H) = Nat.card U := by
    have h3 : Nat.card ↥(U ⊓ H) = Nat.card ((U ⊓ H).subgroupOf U) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    rw [h3, Subgroup.inf_subgroupOf_left]
    exact Subgroup.index_mul_card _
  have h4 : (H.relIndex U : ℚ) ≠ 0 := by
    have : Nat.card U ≠ 0 := Nat.card_pos.ne'
    rw [← h2] at this
    exact Nat.cast_ne_zero.mpr (left_ne_zero_of_mul this)
  have h5 : ((U ⊔ H).index : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have h6 : (Nat.card ↥(U ⊓ H) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← h1, ← h2]
  push_cast
  field_simp

theorem avgCondExp_annihilator (H : Subgroup (ZMod N)ˣ) :
    avgCondExp l (annihilator ℂ (H : Set (ZMod N)ˣ)) =
      ∑ t ∈ Finset.range (N.factorization l),
        (1 - (Nat.card ↥(higherUnits N l t ⊓ H) : ℚ) / (Nat.card (higherUnits N l t) : ℚ)) := by
  classical
  set X := annihilator ℂ (H : Set (ZMod N)ˣ) with hX
  haveI : Fintype X := Fintype.ofFinite X
  have hX0 : (Nat.card X : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hc : ∀ ψ : DirichletCharacter ℂ N, (condExp l ψ : ℚ) =
      ∑ t ∈ Finset.range (N.factorization l),
        (1 - if ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) then (1 : ℚ) else 0) := by
    intro ψ
    have hle : condExp l ψ ≤ N.factorization l :=
      (Nat.factorization_le_iff_dvd ψ.conductor_ne_zero (NeZero.ne N)).mpr ψ.conductor_dvd_level l
    have h1 : ∀ t ∈ Finset.range (N.factorization l),
        (1 - if ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) then (1 : ℚ) else 0) =
          if t < condExp l ψ then 1 else 0 := by
      intro t ht
      have := filt_mem_ann l (Finset.mem_range.mp ht).le ψ
      by_cases h : t < condExp l ψ
      · rw [if_neg (by rw [this]; omega), if_pos h, sub_zero]
      · rw [if_pos (by rw [this]; omega), if_neg h, sub_self]
    rw [Finset.sum_congr rfl h1, Finset.sum_boole]
    have : (Finset.range (N.factorization l)).filter (fun t => t < condExp l ψ) =
        Finset.range (condExp l ψ) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  rw [avgCondExp, finsum_eq_sum_of_fintype]
  simp only [hc]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← filt_index, ← filt_card_ann, ← filt_card_ann H, ← hX, Finset.sum_sub_distrib,
    Finset.sum_boole, sub_div]
  congr 1
  · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one,
      div_self hX0]
  · congr 2
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X)
      (· ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ))).trans
        (Equiv.subtypeEquivRight fun ψ => (filt_ann_sup _ _ ψ).symm))

theorem rootWeight_eq_sum (g : (ZMod N)ˣ) (hg : g ≠ 1) :
    rootWeight l (addOrderOf ((g : ZMod N) - 1)) =
      ∑ t ∈ Finset.range (N.factorization l),
        Set.indicator (higherUnits N l t : Set (ZMod N)ˣ)
          (fun _ => 1 / (Nat.card (higherUnits N l t) : ℚ)) g := by
  classical
  have hl : l.Prime := Fact.out
  have hm1 : addOrderOf ((g : ZMod N) - 1) ≠ 1 := by
    rw [Ne, AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero]
    exact fun h => hg (Units.ext h)
  have hmN : addOrderOf ((g : ZMod N) - 1) ∣ N := by
    simpa using addOrderOf_dvd_card (x := (g : ZMod N) - 1)
  unfold rootWeight
  split_ifs with h
  · obtain ⟨-, s, hs⟩ := h
    have hs1 : s ≠ 0 := by rintro rfl; exact hm1 (by simpa using hs)
    have hsv : s ≤ N.factorization l := by
      rw [hs] at hmN
      exact (hl.pow_dvd_iff_le_factorization (NeZero.ne N)).mp hmN
    have h1 : ∀ t ∈ Finset.range (N.factorization l),
        Set.indicator (higherUnits N l t : Set (ZMod N)ˣ)
          (fun _ => 1 / (Nat.card (higherUnits N l t) : ℚ)) g =
        if t < N.factorization l - s + 1 then
          (Nat.totient (l ^ t) : ℚ) / (Nat.totient (l ^ N.factorization l) : ℚ) else 0 := by
      intro t ht
      have ht' := (Finset.mem_range.mp ht).le
      have h2 := filt_mem_higher l ht' g
      rw [hs, Nat.pow_dvd_pow_iff_le_right hl.one_lt] at h2
      rw [Set.indicator_apply]
      refine if_congr (h2.trans (by omega)) ?_ rfl
      rw [← filt_card_higher l ht']
      have h3 : (Nat.totient (l ^ t) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (pow_pos hl.pos _)).ne'
      have h4 : (Nat.card (higherUnits N l t) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      push_cast
      field_simp
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have : (Finset.range (N.factorization l)).filter (fun t => t < N.factorization l - s + 1) =
        Finset.range (N.factorization l - s + 1) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, filt_telescope l (by omega), hs, Nat.sub_sub_self hsv]
  · symm
    refine Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (fun hm => h ⟨hm1, ?_⟩) _
    have h2 := (filt_mem_higher l (Finset.mem_range.mp ht).le g).mp hm
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow hl).mp h2
    exact ⟨s, hs⟩

open Classical in

theorem sum_rootWeight_eq_avgCondExp (H : Subgroup (ZMod N)ˣ) :
    ∑ g ∈ Finset.univ.filter (fun g : (ZMod N)ˣ => g ∉ H),
        rootWeight l (addOrderOf ((g : ZMod N) - 1)) =
      avgCondExp l (annihilator ℂ (H : Set (ZMod N)ˣ)) := by
  rw [avgCondExp_annihilator, Finset.sum_congr rfl (fun g hg => rootWeight_eq_sum l g
    (by rintro rfl; exact (Finset.mem_filter.mp hg).2 H.one_mem)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  generalize higherUnits N l t = U
  have h4 : (Nat.card U : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp only [Set.indicator_apply, SetLike.mem_coe]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_comm]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun g : (ZMod N)ˣ => g ∈ U)) (fun g => g ∈ H)
  have h2 : (Finset.univ.filter (fun g : (ZMod N)ˣ => g ∈ U)).card = Nat.card U := by
    rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
  have h3 : ((Finset.univ.filter (fun g : (ZMod N)ˣ => g ∈ U)).filter (fun g => g ∈ H)).card =
      Nat.card ↥(U ⊓ H) := by
    rw [Finset.filter_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  rw [h2, h3] at h1
  have h5 := congrArg (Nat.cast : ℕ → ℚ) h1
  push_cast at h5
  field_simp
  linarith

end KStar.Ram
