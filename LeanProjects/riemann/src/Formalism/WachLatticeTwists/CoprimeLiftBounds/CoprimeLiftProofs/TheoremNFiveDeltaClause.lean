import Formalism.WachLatticeTwists.CoprimeLiftBounds.WachTwistTheoremDeltaClause
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveTopHolds
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SelmerInjColumnPlace
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG IsDiscreteValuationRing

namespace DeltaValuation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma unit_add {w a : O} (hw : IsUnit w) (ha : ¬ IsUnit a) : IsUnit (w + a) := by
  by_contra h
  have h1 : w + a ∈ nonunits O := h
  have h2 : -a ∈ nonunits O := by
    intro hh
    exact ha (by simpa using hh.neg)
  have h3 := IsLocalRing.nonunits_add h1 h2
  rw [add_neg_cancel_right] at h3
  exact h3 hw

lemma nonunit_mul {a : O} (ha : ¬ IsUnit a) (b : O) : ¬ IsUnit (a * b) :=
  fun h => ha (isUnit_of_mul_isUnit_left h)

lemma unit_of_coprime {l m : ℕ} (hl : ¬ IsUnit (l : O)) (h : Nat.Coprime m l) : IsUnit (m : O) := by
  have h1 : IsCoprime (m : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  obtain ⟨a, b, hab⟩ := h1
  have h2 : (a : O) * (m : O) + (b : O) * (l : O) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  by_contra hm
  have h3 : (a : O) * (m : O) + (b : O) * (l : O) ∈ nonunits O :=
    IsLocalRing.nonunits_add (by rw [mul_comm]; exact nonunit_mul hm _)
      (by rw [mul_comm]; exact nonunit_mul hl _)
  rw [h2] at h3
  exact h3 isUnit_one

lemma geom_unit {l m : ℕ} (hl : ¬ IsUnit (l : O)) (h : Nat.Coprime m l) {x : O}
    (hx : ¬ IsUnit (x - 1)) : IsUnit (∑ i ∈ range m, x ^ i) := by
  have h1 : x - 1 ∣ (∑ i ∈ range m, x ^ i) - m := by
    have : (∑ i ∈ range m, x ^ i) - m = ∑ i ∈ range m, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨c, hc⟩ := h1
  have : ∑ i ∈ range m, x ^ i = (m : O) + (x - 1) * c := by rw [← hc]; ring
  rw [this]
  exact unit_add (unit_of_coprime hl h) (nonunit_mul hx c)

lemma step {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) :
    ∃ y : Oˣ, x ^ l - 1 = (l : O) ^ (s + 1) * y := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hx : x = 1 + (l : O) * ((l : O) ^ s' * y) := by
    have : x = 1 + (x - 1) := by ring
    rw [this, hy]; ring
  have hsum : ∃ w : Oˣ, ∑ i ∈ range l, x ^ i = (l : O) * w := by
    by_cases h2 : l = 2
    · subst h2
      obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by have := hs2 rfl; omega⟩
      have hu : IsUnit (1 + ((2 : ℕ) : O) * (((2 : ℕ) : O) ^ s'' * y)) :=
        unit_add isUnit_one (nonunit_mul hl _)
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec, Finset.sum_range_succ, Finset.sum_range_one, hx]
      push_cast
      ring
    · have hodd : Odd l := hp.odd_of_ne_two h2
      obtain ⟨c, hc⟩ := odd_sq_dvd_geom_sum₂_sub (R := O) (a := 1) (b := (l : O) ^ s' * y) hodd
      have hu : IsUnit (1 + (l : O) * c) := unit_add isUnit_one (nonunit_mul hl _)
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec]
      simp only [one_pow, mul_one] at hc
      rw [← hx] at hc
      have : ∑ i ∈ range l, x ^ i = (l : O) + (l : O) ^ 2 * c := by rw [← hc]; ring
      rw [this]; ring
  obtain ⟨w, hw⟩ := hsum
  refine ⟨y * w, ?_⟩
  rw [← mul_geom_sum, hy, hw]
  push_cast
  ring

lemma iter {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) (k : ℕ) :
    ∃ y : Oˣ, x ^ (l ^ k) - 1 = (l : O) ^ (s + k) * y := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := step hp hl (x ^ (l ^ k)) (s + k) (by omega) (fun h2 => by have := hs2 h2; omega) ih
    rwa [← pow_mul, ← pow_succ, add_assoc] at this

lemma pow_sub_one {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) (n : ℕ) (hn : n ≠ 0) :
    ∃ y : Oˣ, x ^ n - 1 = (l : O) ^ (s + padicValNat l n) * y := by
  have : Fact l.Prime := ⟨hp⟩
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hp.ne_one
  have hm0 : m ≠ 0 := fun h0 => hm (by rw [h0]; exact dvd_zero _)
  have hv : padicValNat l (l ^ k * m) = k := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨y, hy⟩ := iter hp hl x s hs hs2 h k
  have hnu : ¬ IsUnit (x ^ (l ^ k) - 1) := by
    rw [hy, show s + k = (s + k - 1) + 1 by omega, pow_succ', mul_assoc]
    exact nonunit_mul hl _
  have hg := geom_unit hl ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm hnu
  refine ⟨y * hg.unit, ?_⟩
  rw [hv, pow_mul, ← mul_geom_sum, hy]
  push_cast
  rw [IsUnit.unit_spec]
  ring

end DeltaValuation

theorem powSubOneO : StatPowSubOneO := by
  intro O _ _ _ ℓ hℓ hℓu s₀ hs hs2 x y hx n hn
  obtain ⟨w, hw⟩ := DeltaValuation.pow_sub_one hℓ hℓu x s₀ hs hs2 ⟨y, hx⟩ n hn
  rw [hw, addVal_mul, addVal_pow, addVal_eq_zero_of_unit, add_zero, nsmul_eq_mul, mul_comm]

theorem theorem_n_five_delta_sum : WachTwistTheoremDeltaSum := by
  intro ℓ hℓ s₀ t
  have : Fact ℓ.Prime := ⟨hℓ⟩
  induction t with
  | zero =>
    rw [show Finset.Ioo 0 (0 + 1) = ∅ from by
      ext i; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega]
    simp
  | succ t ih =>
    have h : Finset.Ioo 0 (t + 1 + 1) = insert (t + 1) (Finset.Ioo 0 (t + 1)) := by
      ext i; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
    rw [h, Finset.sum_insert (by simp), ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t)]
    ring

theorem theorem_n_five_delta_clause : WachTwistTheoremDeltaClause := by
  intro O _ _ _ ℓ hℓ hℓu s₀ hs hs2 x y u₁ hx t δO eO
  have he : eO = addVal O (ℓ : O) := IdempotentNormalFormsLenFacts.length_quot_span _
  have hfac : ∀ i ∈ Finset.Ioo 0 t, addVal O ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O)) =
      eO * ((s₀ + padicValNat ℓ i : ℕ) : ℕ∞) := by
    intro i hi
    have hi0 : i ≠ 0 := by rw [Finset.mem_Ioo] at hi; omega
    have h1 : ((x⁻¹ ^ i : Oˣ) : O) * (x : O) ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have h2 : (u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O) =
        ((u₁ * x⁻¹ ^ i : Oˣ) : O) * ((x : O) ^ i - 1) := by
      rw [Units.val_mul, mul_sub, mul_assoc, h1]; ring
    rw [h2, addVal_mul, addVal_eq_zero_of_unit, zero_add,
      powSubOneO O ℓ hℓ hℓu s₀ hs hs2 x y hx i hi0, he]
  have hval : addVal O δO = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) := by
    show addVal O (∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O))) = _
    rw [IdempotentNormalFormsLenFacts.addVal_prod, Finset.sum_congr rfl hfac, ← Finset.mul_sum, Nat.cast_sum]
  refine ⟨hval, ?_⟩
  rw [hval]
  have hle : ∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) ≤ t * s₀ + padicValNat ℓ t.factorial := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    cases t with
    | zero => simp
    | succ t =>
      rw [theorem_n_five_delta_sum ℓ hℓ s₀ t, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t)]
      exact add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ t)) (Nat.le_add_left _ _)
  gcongr

theorem deltaPt : StatDeltaPt := by
  intro O Tc M _ _ _ _ _ t rr a h m
  have key : ∀ s : Finset ℕ, (∀ i ∈ s, 0 < t ∧ i < t) → ∀ m : M,
      (∏ i ∈ s, (rr 0 - rr i)) • m = (∏ i ∈ s, (a 0 - a i)) • m := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ m; simp
    | insert i s hi ih =>
      intro hs m
      obtain ⟨h0, hit⟩ := hs i (Finset.mem_insert_self i s)
      rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_smul, mul_smul,
        ih (fun k hk => hs k (Finset.mem_insert_of_mem hk)) m, sub_smul, sub_smul, h 0 h0, h i hit]
  exact key _ (fun i hi => by rw [Finset.mem_Ioo] at hi; omega) m

theorem inputs_from_selmer_inj : SelmerInjConditions := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ _ colIdx D j e' Kc k0 ℓ what₂ s
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo Io ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam
    Cs _ _ cls pr Fs Im h
  obtain ⟨h1, h2, h3, h4, ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun l => ?_, h6⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := a8 l
  exact selmer_inj_column_place O A T' G M L V r χ (D (colIdx l)) iL qV tens a1 a2 a3 a4 a5 a6 a7 (Ff l)
    (j (colIdx l)) (κ l) (κz l) b1 b2 b3 b4 b5

set_option maxHeartbeats 4000000 in
theorem theorem_n_five_top_variant : WachTwistTheoremVariant := by
  intro O _ _ _ X X' T T' Z p q b ha hb d _ _ R' _ hc Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ colIdx hinj
    D j e' Kc k0 hEE hee hpts g₀ n hspan π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard hcard1
    sE tE δO ℓ cB what₂ qs deg s vhE H0 Sha hEsum hk0 NNc cols eO vδ N h0
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ
    lam Cs _ _ cls pr Fs Im cT I γQ ζ ζO nQ u rr gI s₀ u₁ y hℓ hℓu hs hs2 hx hδ hδO hrr
    hE0 hτ0 hne hIn0 hC hOne
  have hδm : ∀ (c : Fin (t + 1)) (m : blockRestrictedRepresentationType bl ρk c), δ • m = δO • m := by
    intro c m
    have h := deltaPt O Tc (blockRestrictedRepresentationType bl ρk c) t rr
      (fun i => (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) (hrr c) m
    simp only [pow_zero, Units.val_one, mul_one] at h
    rw [hδ, hδO]
    exact h
  obtain ⟨hv1, hv2⟩ := theorem_n_five_delta_clause O ℓ hℓ hℓu s₀ hs hs2 (ε gI) y u₁ hx t
  refine ⟨?_, ?_, ?_⟩
  · exact theorem_n_five_top_holds O X X' T T' Z p q b ha hb d R' hc Tc G r χ E e₁ δ ι colIdx hinj D j e' Kc k0 hEE hee
      hpts g₀ n hspan π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard hcard1 sE tE δO ℓ cB what₂ qs deg
      s vhE H0 Sha hEsum hk0 L tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr
      Fs Im cT I γQ ζ ζO nQ u hE0 (hδm 0) hτ0 hne
      (inputs_from_selmer_inj O R' Tc G (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ ι colIdx D j e' Kc k0 ℓ what₂ s L tens v₁ κ V
        iL qV Ff κz (HcG 0) (Hc 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr Fs Im hIn0)
      (fun c hc2 => by
        obtain ⟨a1, a2, a4, a5, a6⟩ := hC c hc2
        exact ⟨a1, a2, hδm c, a4, a5, a6⟩)
      (by
        obtain ⟨a1, a2, a3, a5, a6, a7, a8, a9⟩ := hOne
        exact ⟨a1, a2, a3, hδm _, a5, a6, a7, a8, a9⟩)
  · show addVal O δO = _
    rw [hδO]
    exact hv1
  · show addVal O δO ≤ _
    rw [hδO]
    exact hv2

end Formalism.RepresentationBoundsCohomology.BR
