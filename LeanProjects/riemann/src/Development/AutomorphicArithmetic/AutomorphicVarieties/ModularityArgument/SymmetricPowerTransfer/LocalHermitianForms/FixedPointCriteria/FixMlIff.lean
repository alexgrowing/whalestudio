import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsFixPOrderPowIffLeAndAssocPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsUnitSmulOrderOfMemGs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrderLevelInjectiveOfSmulEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NcardUnitTranslatesOrderEqRelIndex

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.PK

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

theorem fix_ml_iff {S : Set (Etau K τ)} {t : K} (a : (Etau K τ)ˣ) :
    IsFixP O τ t (PS.ml a S) ↔ IsFixP O τ (t * PS.nU a) S := by
  refine ⟨fun h => ?_, PS.fix_ml a⟩
  have h1 : IsFixP O τ (t * PS.nU a) (PS.ml a⁻¹ (PS.ml a S)) := by
    refine PS.fix_ml _ ?_
    rwa [mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, mul_one]
  rwa [← PS.ml_mul, inv_mul_cancel, PS.ml_one] at h1

theorem Gu_le_C : Gu O τ ≤ Cint O τ := fun _ hu => PS.mem_C_of_int hu.1 hu.2

theorem sc_Gu {v : Oˣ} {s : Kˣ} (h : algebraMap O K v = s) : PS.sc τ s ∈ Gu O τ := by
  have hs' : algebraMap O K ((v⁻¹ : Oˣ) : O) = ((s⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val s, ← h]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  change IsIntegral O ((PS.sc τ s : (Etau K τ)ˣ) : Etau K τ) ∧
    IsIntegral O (((PS.sc τ s)⁻¹ : (Etau K τ)ˣ) : Etau K τ)
  constructor
  · rw [PS.sc_val, ← h, ← algebraMap_etau]
    exact isIntegral_algebraMap
  · rw [← map_inv, PS.sc_val, ← hs', ← algebraMap_etau]
    exact isIntegral_algebraMap

theorem yy_int {π : O} {m : ℕ} {x : Etau K τ} (hx : IsIntegral O x) : IsIntegral O (yy π m x) := by
  show IsIntegral O (algebraMap O K (π ^ m) • x)
  rw [Algebra.smul_def, ← algebraMap_etau]
  exact isIntegral_algebraMap.mul hx

theorem gen_ord {y : Etau K τ} (hy : IsIntegral O y) : PS.Gen O τ (Ord O y) 1 := by
  refine ⟨Submodule.subset_span (by simp), fun w hw => ?_⟩
  have hle : Submodule.span O ({1, y} : Set (Etau K τ)) ≤
      Subalgebra.toSubmodule (integralClosure O (Etau K τ)) := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
    rcases hz with rfl | rfl
    · exact isIntegral_one
    · exact hy
  have hw' := hle hw
  simp only [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at hw'
  simpa using hw'

variable [IsDomain O] [IsDiscreteValuationRing O] {Δ : K}

theorem nU_Gu (L : IsLoc O Δ) {u : (Etau K τ)ˣ} (hu : u ∈ Gu O τ) : ∃ v : Oˣ, algebraMap O K v = (PS.nU u : K) := by
  haveI := L.frac
  have key : ∀ w : (Etau K τ)ˣ, IsIntegral O (w : Etau K τ) → ∃ b : O, algebraMap O K b = (PS.nU w : K) := fun w hw =>
    int_down (τ := τ) L _ (by
      rw [PS.nU_val, algebraMap_norm_eq_mul_star]; exact hw.mul (PS.star_int hw))
  obtain ⟨b, hb⟩ := key u hu.1
  obtain ⟨b', hb'⟩ := key u⁻¹ hu.2
  have h1 : b * b' = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, hb, hb', ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one]
  exact ⟨Units.mkOfMulEqOne _ _ h1, hb⟩

theorem fix_lv (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {π : O} {n : ℕ} {e : Oˣ} {h : O} {x : Etau K τ}
    (C : Cond π n e h x) (t : K) (r : Kˣ) {u : (Etau K τ)ˣ} (hu : u ∈ Gu O τ) (m : ℕ) :
    IsFixP O τ t (PS.ml (PS.sc τ r * u) (Ord O (yy π m x))) ↔
      m ≤ n ∧ ∃ w : Oˣ, t * (r : K) ^ 2 * algebraMap O K (π ^ m) = algebraMap O K w * algebraMap O K (π ^ n) := by
  obtain ⟨v, hv⟩ := nU_Gu L hu
  have hvi : algebraMap O K v * algebraMap O K (v⁻¹ : Oˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have e1 : ((PS.nU (PS.sc τ r * u) : Kˣ) : K) = (r : K) ^ 2 * algebraMap O K v := by
    rw [map_mul, PS.nU_sc, Units.val_mul, hv, Units.val_pow_eq_pow_val]
  rw [fix_ml_iff, UpperTheory.isFixP_order_pow_iff_le_and_assoc_pow O K Δ τ L hτ π n e h x C, e1]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    refine ⟨w * v⁻¹, ?_⟩
    rw [Units.val_mul, map_mul]
    linear_combination (algebraMap O K (v⁻¹ : Oˣ)) * hw - (t * (r : K) ^ 2 * algebraMap O K (π ^ m)) * hvi
  · rintro ⟨w, hw⟩
    refine ⟨w * v, ?_⟩
    rw [Units.val_mul, map_mul]
    linear_combination (algebraMap O K v) * hw

private theorem ml_sc_mul_mem_gs_of_val_eq (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {π : O} {n : ℕ} {e : Oˣ} {h : O}
    {x : Etau K τ} (C : Cond π n e h x) (t : Kˣ) (r : Kˣ) {u : (Etau K τ)ˣ} (hu : u ∈ Gu O τ) (m : ℕ)
    (hm : m ≤ n) (hw : ∃ w : Oˣ, (t : K) * (r : K) ^ 2 * algebraMap O K (π ^ m) =
      algebraMap O K w * algebraMap O K (π ^ n)) :
    PS.ml (PS.sc τ r * u) (Ord O (yy π m x)) ∈ PS.Gs O τ t 1 := by
  have hg := PS.gen_ml (gen_ord (yy_int (π := π) (m := m) C.gen.int)) (PS.sc τ r * u)
  rw [mul_one] at hg
  refine ⟨(fix_lv L hτ C t r hu m).2 ⟨hm, hw⟩, PS.sc τ r * u,
    mul_mem (PS.sc_mem r) (Gu_le_C hu), ?_⟩
  rwa [one_mul]

private theorem evenVal_mul_pi_pow_iff_exists_sq_unit (L : IsLoc O Δ) {π : O} (hπ : π ≠ 0) (t : K) (n m : ℕ) :
    EvenVal O (t * algebraMap O K (π ^ (n + m))) ↔
      ∃ r : Kˣ, ∃ w : Oˣ, t * (r : K) ^ 2 * algebraMap O K (π ^ m) =
        algebraMap O K w * algebraMap O K (π ^ n) := by
  haveI := L.frac
  have hP : algebraMap O K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hπ
  have hPn : algebraMap O K π ^ n ≠ 0 := pow_ne_zero _ hP
  simp only [pow_add, map_mul, map_pow]
  constructor
  · rintro ⟨u, s, hs, he⟩
    refine ⟨Units.mk0 (algebraMap O K π ^ n / s) (div_ne_zero hPn hs), u, ?_⟩
    simp only [Units.val_mk0]
    field_simp
    linear_combination he
  · rintro ⟨r, w, hrw⟩
    refine ⟨w, algebraMap O K π ^ n / r, div_ne_zero hPn r.ne_zero, ?_⟩
    field_simp
    linear_combination hrw

private theorem eq_of_ml_ord_yy_eq (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {π : O} {n : ℕ} {e : Oˣ} {h : O}
    {x : Etau K τ} (C : Cond π n e h x) {w w' : (Etau K τ)ˣ} {m m' : ℕ}
    (hh : PS.ml w (Ord O (yy π m x)) = PS.ml w' (Ord O (yy π m' x))) : m = m' := by
  apply order_level_injective_of_smul_eq O K Δ τ L hτ π n e h x C (w'⁻¹ * w) m m'
  rw [PS.ml_mul, hh, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]

private theorem exists_unit_eq_div_of_same_scaling (L : IsLoc O Δ) {π : O} (hπ : π ≠ 0) (t r r' : Kˣ) (n m : ℕ) (w w' : Oˣ)
    (hrw : (t : K) * (r : K) ^ 2 * algebraMap O K (π ^ m) = algebraMap O K w * algebraMap O K (π ^ n))
    (hw' : (t : K) * (r' : K) ^ 2 * algebraMap O K (π ^ m) = algebraMap O K w' * algebraMap O K (π ^ n)) :
    ∃ v : Oˣ, algebraMap O K v = ((r' / r : Kˣ) : K) := by
  haveI := L.frac
  have hPn : algebraMap O K (π ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (pow_ne_zero _ hπ)
  have e1 : algebraMap O K w' * (r : K) ^ 2 = algebraMap O K w * (r' : K) ^ 2 := by
    apply mul_right_cancel₀ hPn
    linear_combination (-(r : K) ^ 2) * hw' + (r' : K) ^ 2 * hrw
  have hinv : algebraMap O K (w' : O) * algebraMap O K ((w'⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  apply PS.unit_of_sq L (ε := w * w'⁻¹)
  rw [Units.val_mul, map_mul, Units.val_div_eq_div_val]
  have hr := r.ne_zero
  field_simp
  linear_combination (-(r : K) ^ 2) * hinv + algebraMap O K ((w'⁻¹ : Oˣ) : O) * e1

open Classical in
theorem gs_count (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {π : O} {n : ℕ} {e : Oˣ} {h : O} {x : Etau K τ}
    (C : Cond π n e h x) (t : Kˣ) :
    (PS.Gs O τ t 1).ncard = ∑ m ∈ Finset.range (n + 1),
      if EvenVal O ((t : K) * algebraMap O K (π ^ (n + m))) then (Hu O (yy π m x)).relIndex (Gu O τ) else 0 := by
  classical
  have hπ : π ≠ 0 := C.irr.ne_zero
  have hfin := PS.gs_fin L hτ t 1
  have hlev : ∀ S ∈ PS.Gs O τ (t : K) 1, ∃ m, ∃ r : Kˣ, ∃ u ∈ Gu O τ, m ≤ n ∧
      (∃ w : Oˣ, (t : K) * (r : K) ^ 2 * algebraMap O K (π ^ m) =
        algebraMap O K w * algebraMap O K (π ^ n)) ∧
      S = PS.ml (PS.sc τ r * u) (Ord O (yy π m x)) := by
    intro S hG
    obtain ⟨m, r, u, hu, hS⟩ := exists_unit_smul_order_of_mem_gs O K Δ τ L hτ π n e h x C t S hG
    have hG' : IsFixP O τ t S ∧ _ := hG
    have hfx := (fix_lv L hτ C t r hu m).1 (by rw [← hS]; exact hG'.1)
    exact ⟨m, r, u, hu, hfx.1, hfx.2, hS⟩
  have hpiece : ∀ m ≤ n, {S | S ∈ PS.Gs O τ (t : K) 1 ∧ ∃ w : (Etau K τ)ˣ, S = PS.ml w (Ord O (yy π m x))}.ncard =
      if EvenVal O ((t : K) * algebraMap O K (π ^ (n + m))) then (Hu O (yy π m x)).relIndex (Gu O τ) else 0 := by
    intro m hm
    by_cases hev : EvenVal O ((t : K) * algebraMap O K (π ^ (n + m)))
    · rw [if_pos hev]
      obtain ⟨r, w, hrw⟩ := (evenVal_mul_pi_pow_iff_exists_sq_unit L hπ (t : K) n m).1 hev
      rw [← ncard_unit_translates_order_eq_relIndex O K τ (PS.sc τ r) (yy π m x)]
      congr 1
      ext S
      constructor
      · rintro ⟨hG, w0, hw0⟩
        obtain ⟨m', r', u', hu', hm', ⟨w', hw'⟩, hS⟩ := hlev S hG
        have hmm : m = m' := eq_of_ml_ord_yy_eq L hτ C (hw0.symm.trans hS)
        subst hmm
        obtain ⟨v, hv⟩ := exists_unit_eq_div_of_same_scaling L hπ t r r' n m w w' hrw hw'
        refine ⟨PS.sc τ (r' / r) * u', mul_mem (sc_Gu hv) hu', ?_⟩
        rw [hS, ← mul_assoc, ← map_mul, mul_div_cancel]
      · rintro ⟨u, hu, hS⟩
        exact ⟨hS ▸ ml_sc_mul_mem_gs_of_val_eq L hτ C t r hu m hm ⟨w, hrw⟩, _, hS⟩
    · rw [if_neg hev]
      rw [Set.ncard_eq_zero (Set.Finite.subset hfin (fun S hS => hS.1))]
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hG, w0, hw0⟩
      obtain ⟨m', r', u', hu', hm', ⟨w', hw'⟩, hS⟩ := hlev S hG
      have hmm : m = m' := eq_of_ml_ord_yy_eq L hτ C (hw0.symm.trans hS)
      subst hmm
      exact hev ((evenVal_mul_pi_pow_iff_exists_sq_unit L hπ (t : K) n m).2 ⟨r', w', hw'⟩)
  have hsplit : hfin.toFinset = (Finset.range (n + 1)).biUnion (fun m => hfin.toFinset.filter
      (fun S => ∃ w : (Etau K τ)ˣ, S = PS.ml w (Ord O (yy π m x)))) := by
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · intro hG
      obtain ⟨m, r, u, hu, hm, -, hS⟩ := hlev S hG
      exact ⟨m, Nat.lt_succ_of_le hm, hG, _, hS⟩
    · rintro ⟨m, -, hG, -⟩
      exact hG
  rw [Set.ncard_eq_toFinset_card _ hfin, hsplit, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [← hpiece m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), ← Set.ncard_coe_finset]
    congr 1
    ext S
    simp
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S hSa hSb
    simp only [Finset.mem_filter] at hSa hSb
    obtain ⟨-, wa, ha⟩ := hSa
    obtain ⟨-, wb, hb⟩ := hSb
    exact hab (eq_of_ml_ord_yy_eq L hτ C (ha.symm.trans hb))

end UpperTheory.V.Z.Sym.Loc.PK
