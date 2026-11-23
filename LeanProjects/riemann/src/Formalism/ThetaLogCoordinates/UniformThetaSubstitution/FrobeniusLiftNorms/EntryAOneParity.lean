import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace ValuationParity

def par (ν : ℕ) : ZMod (2 * ν) →+* ZMod 2 := ZMod.castHom (Dvd.intro ν rfl) (ZMod 2)

lemma par_eq {ν : ℕ} [NeZero ν] (x : ZMod (2 * ν)) : par ν x = ((x.val : ℕ) : ZMod 2) := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  show ZMod.cast x = _
  exact ZMod.cast_eq_val x

lemma val_mod_two {ν : ℕ} [NeZero ν] (x : ZMod (2 * ν)) : x.val % 2 = (par ν x).val := by
  rw [par_eq, ZMod.val_natCast]

lemma par_odd {ν : ℕ} (y : ZMod (2 * ν)) : par ν (1 + 2 * y) = 1 := by
  rw [map_add, map_one, map_mul]
  have h2 : par ν 2 = 0 := by
    rw [map_ofNat]
    rfl
  rw [h2, zero_mul, add_zero]

lemma val_odd {ν : ℕ} [NeZero ν] {x y : ZMod (2 * ν)} (h : x = 1 + 2 * y) : x.val % 2 = 1 := by
  rw [val_mod_two, h, par_odd]
  rfl

lemma parity_ne {ν : ℕ} [NeZero ν] {s s' y : ZMod (2 * ν)} (h : s' - s = 1 + 2 * y) :
    s'.val % 2 ≠ s.val % 2 := by
  rw [val_mod_two, val_mod_two]
  have hs : par ν s' = par ν s + 1 := by
    rw [show s' = s + (1 + 2 * y) by rw [← h]; ring, map_add, par_odd]
  rw [hs]
  generalize par ν s = a
  revert a
  decide

lemma isLeast_val {n : ℕ} [NeZero n] (s s' : ZMod n) (h : 1 ≤ (s' - s).val) :
    IsLeast {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} (s' - s).val := by
  refine ⟨⟨h, by rw [ZMod.natCast_zmod_val]; ring⟩, ?_⟩
  rintro e ⟨_, he⟩
  have he' : ((e : ℕ) : ZMod n) = s' - s := by rw [← he]; ring
  rw [← he', ZMod.val_natCast]
  exact Nat.mod_le _ _

lemma charge_exists (hL : ChargeLemma) {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (hp : 1 ≤ p)
    (φ : PhiI ν r0 r1 E) :
    ∃ s s' : ZMod (2 * ν), ((s = pairFirst φ ∧ s' = pairSecond φ) ∨ (s = pairSecond φ ∧ s' = pairFirst φ)) ∧
      (s' - s).val % 2 = 1 ∧ s'.val % 2 ≠ s.val % 2 ∧
      p ^ (s' - s).val ≤ dAof p φ (s, φ.2.2.2.2) := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  have hA1 : p ^ (1 + 2 * φ.2.1.val) ≤ dAof p φ (pairFirst φ, φ.2.2.2.2) := by
    simp only [dAof, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_right _ _
  have hA2 : p ^ (2 * φ.2.2.1.val) ≤ dAof p φ (pairSecond φ, φ.2.2.2.2) := by
    simp only [dAof, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_left _ _
  by_cases hij : φ.2.2.1.val ≤ φ.2.1.val
  · have hodd : pairSecond φ - pairFirst φ = 1 + 2 * ((φ.2.1.val : ZMod (2 * ν)) - (φ.2.2.1.val : ZMod (2 * ν))) := by
      unfold pairFirst pairSecond
      ring
    have hv := val_odd hodd
    have heq : pairFirst φ + ((1 + 2 * φ.2.1.val : ℕ) : ZMod (2 * ν)) =
        pairSecond φ + ((2 * φ.2.2.1.val : ℕ) : ZMod (2 * ν)) := by
      unfold pairFirst pairSecond
      push_cast
      ring
    have hd := hL (2 * ν) (pairFirst φ) (pairSecond φ) (1 + 2 * φ.2.1.val) (2 * φ.2.2.1.val) _ (by omega) heq
      (isLeast_val (pairFirst φ) (pairSecond φ) (by omega))
    exact ⟨pairFirst φ, pairSecond φ, Or.inl ⟨rfl, rfl⟩, hv, parity_ne hodd,
      le_trans (Nat.pow_le_pow_right hp hd) hA1⟩
  · have hodd : pairFirst φ - pairSecond φ =
        1 + 2 * ((φ.2.2.1.val : ZMod (2 * ν)) - (φ.2.1.val : ZMod (2 * ν)) - 1) := by
      unfold pairFirst pairSecond
      ring
    have hv := val_odd hodd
    have heq : pairSecond φ + ((2 * φ.2.2.1.val : ℕ) : ZMod (2 * ν)) =
        pairFirst φ + ((1 + 2 * φ.2.1.val : ℕ) : ZMod (2 * ν)) := by
      unfold pairFirst pairSecond
      push_cast
      ring
    have hd := hL (2 * ν) (pairSecond φ) (pairFirst φ) (2 * φ.2.2.1.val) (1 + 2 * φ.2.1.val) _ (by omega) heq
      (isLeast_val (pairSecond φ) (pairFirst φ) (by omega))
    exact ⟨pairSecond φ, pairFirst φ, Or.inr ⟨rfl, rfl⟩, hv, parity_ne hodd,
      le_trans (Nat.pow_le_pow_right hp hd) hA2⟩

lemma sum_charge {Φ S : Type} [Fintype Φ] [DecidableEq S] (TT : Finset S) (R : Finset ℕ)
    (c : Φ → S × ℕ) (w : Φ → ℕ) (h : ∀ φ, w φ ≠ 0 → (c φ).1 ∈ TT ∧ (c φ).2 ∈ R) :
    ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0) = ∑ φ, w φ := by
  calc ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0)
      = ∑ s ∈ TT, ∑ φ, ∑ e ∈ R, (if c φ = (s, e) then w φ else 0) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ φ, ∑ s ∈ TT, ∑ e ∈ R, (if c φ = (s, e) then w φ else 0) := Finset.sum_comm
    _ = ∑ φ, w φ := by
      refine Finset.sum_congr rfl fun φ _ => ?_
      by_cases hw : w φ = 0
      · simp [hw]
      obtain ⟨h1, h2⟩ := h φ hw
      rw [Finset.sum_eq_single (c φ).1]
      · rw [Finset.sum_eq_single (c φ).2]
        · simp
        · intro e _ he
          rw [if_neg]
          intro hc
          apply he
          rw [hc]
        · intro h'
          exact absurd h2 h'
      · intro s _ hs
        refine Finset.sum_eq_zero fun e _ => ?_
        rw [if_neg]
        intro hc
        apply hs
        rw [hc]
      · intro h'
        exact absurd h1 h'

lemma level_le {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (e : TpV ν r1 → ℕ) (α : PhiI ν r0 r1 E → ℕ)
    (β : KapI ν r1 E →₀ ℕ)
    (hτ : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ)
    (hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2)) (s : ZMod (2 * ν)) (e' : ℕ) :
    p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
      ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0) ≤ alN e s := by
  have hφ : ∀ φ, (if c φ = (s, e') then p ^ (2 * e' + 1) * α φ else 0) ≤
      ∑ b, α φ * dAof p φ (s, b) := by
    intro φ
    split_ifs with h
    · have h1 := hc φ
      simp only [h] at h1
      calc p ^ (2 * e' + 1) * α φ = α φ * p ^ (2 * e' + 1) := mul_comm _ _
        _ ≤ α φ * dAof p φ (s, φ.2.2.2.2) := Nat.mul_le_mul_left _ h1
        _ ≤ ∑ b, α φ * dAof p φ (s, b) :=
          Finset.single_le_sum (f := fun b => α φ * dAof p φ (s, b)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    · exact Nat.zero_le _
  have hk : ∀ k : KapI ν r1 E, (if (k.1, k.2.1.val) = (s, e') then p ^ (2 * e' + 1) * β k else 0) ≤
      ∑ b, β k * dBof p k (s, b) := by
    intro k
    split_ifs with h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      calc p ^ (2 * e' + 1) * β k = β k * dBof p k (s, k.2.2) := by
            rw [← h1, ← h2]
            simp [dBof, mul_comm]
        _ ≤ ∑ b, β k * dBof p k (s, b) :=
          Finset.single_le_sum (f := fun b => β k * dBof p k (s, b)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    · exact Nat.zero_le _
  calc p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
        ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0)
      = (∑ φ, if c φ = (s, e') then p ^ (2 * e' + 1) * α φ else 0) +
        ∑ k : KapI ν r1 E, (if (k.1, k.2.1.val) = (s, e') then p ^ (2 * e' + 1) * β k else 0) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_ite, mul_zero]
    _ ≤ (∑ φ, ∑ b, α φ * dAof p φ (s, b)) + ∑ k : KapI ν r1 E, ∑ b, β k * dBof p k (s, b) :=
        add_le_add (Finset.sum_le_sum fun φ _ => hφ φ) (Finset.sum_le_sum fun k _ => hk k)
    _ = ∑ b, ((∑ φ, α φ * dAof p φ (s, b)) + ∑ k, β k * dBof p k (s, b)) := by
        rw [Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
    _ ≤ ∑ b, e (s, b) := Finset.sum_le_sum fun b _ => hτ (s, b)
    _ = alN e s := rfl

end ValuationParity

open ValuationParity in

theorem entryExcessBound_of (hS : EntryStar) (hC : HitsCapPos) (hA : ExcessGainBound) (hL : ChargeLemma) : EntryExcessBound := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hyp
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hyp with h0 | ⟨E, α, β, hαTT, hβTT, hτ, hhasse, hbound⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  classical
  have hp : 2 < p := hyp.2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  choose sφ s'φ hor hodd hpar hle using fun φ : PhiI ν r0 r1 E => charge_exists hL p (by omega) φ
  obtain ⟨c, hcdef⟩ : ∃ c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ,
      ∀ φ, c φ = (sφ φ, ((s'φ φ - sφ φ).val - 1) / 2) := ⟨_, fun _ => rfl⟩
  have hc2 : ∀ φ, 2 * (c φ).2 + 1 = (s'φ φ - sφ φ).val := by
    intro φ
    have := hodd φ
    rw [hcdef]
    omega
  have hc1 : ∀ φ, (c φ).1 = sφ φ := fun φ => by rw [hcdef]
  have hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2) := fun φ => by
    rw [hc2, hc1]
    exact hle φ
  have hsTT : ∀ φ, α φ ≠ 0 → sφ φ ∈ TT ∧ s'φ φ ∈ TT := by
    intro φ hα
    obtain ⟨h1, h2⟩ := hαTT φ hα
    rcases hor φ with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · exact ⟨hs1 ▸ h1, hs2 ▸ h2⟩
    · exact ⟨hs1 ▸ h2, hs2 ▸ h1⟩
  obtain ⟨Ee, hEe⟩ : ∃ Ee : Finset ℕ, Ee = (Finset.univ.image fun φ => (c φ).2) ∪
      (Finset.univ.image fun k : KapI ν r1 E => k.2.1.val) := ⟨_, rfl⟩
  obtain ⟨chN, hchN⟩ : ∃ chN : ZMod (2 * ν) → ℕ → ℕ,
      ∀ s e', chN s e' = ∑ φ, if c φ = (s, e') then α φ else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨iN, hiN⟩ : ∃ iN : ZMod (2 * ν) → ℕ → ℕ,
      ∀ s e', iN s e' = ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hlev : ∀ s e', p ^ (2 * e' + 1) * (chN s e' + iN s e') ≤ alN e s := fun s e' => by
    rw [hchN, hiN]
    exact level_le p e α β hτ c hc s e'
  have hcapN : ∀ s e', iN s e' ≤ capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) := by
    intro s e'
    by_contra hlt
    push_neg at hlt
    apply hhasse
    refine hC K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I
      (fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν)))
      (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
      (Finset.univ.filter fun k : KapI ν r1 E => (k.1, k.2.1.val) = (s, e'))
      (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) ?_ ?_ β ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hk
      rw [hk.1, hk.2]
    · intro k hk k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hk hk'
      funext a
      rw [hk.1, hk.2, hk'.1, hk'.2]
    · rw [hiN, ← Finset.sum_filter] at hlt
      exact hlt
  have hcoreA := hA (2 * ν) (p : ℝ) TT (dSet TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
    (deLoss p r0 r1 TT (alN e) (lsN l sf))
    (gamP p * ∑ s ∈ TT, (alN e s : ℝ) - (∑ φ, (α φ : ℝ)) - (∑ k, (β k : ℝ)) -
      deLoss p r0 r1 TT (alN e) (lsN l sf))
    (fun s e' => (iN s e' : ℝ)) (fun s e' => (chN s e' : ℝ)) Ee hp1
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (fun _ _ => Nat.cast_nonneg _) ?hE ?hD ?hmain ?h6 ?h7
  case hE =>
    intro s e' he'
    constructor
    · show (iN s e' : ℝ) = 0
      rw [hiN, Nat.cast_eq_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg]
      intro hk
      apply he'
      simp only [Prod.mk.injEq] at hk
      rw [hEe, ← hk.2]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · show (chN s e' : ℝ) = 0
      rw [hchN, Nat.cast_eq_zero]
      refine Finset.sum_eq_zero fun φ _ => ?_
      rw [if_neg]
      intro hφ
      apply he'
      have he2 : (c φ).2 = e' := by rw [hφ]
      rw [hEe, ← he2]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  case hD =>
    intro s e' hn
    show (chN s e' : ℝ) = 0
    rw [hchN, Nat.cast_eq_zero]
    refine Finset.sum_eq_zero fun φ _ => ?_
    split_ifs with hφ
    · by_contra hα
      apply hn
      obtain ⟨h1, h2⟩ := hsTT φ hα
      have hs : sφ φ = s := by rw [← hc1, hφ]
      have he : (c φ).2 = e' := by rw [hφ]
      rw [dSet, Finset.mem_image]
      refine ⟨s'φ φ, Finset.mem_filter.mpr ⟨h2, ?_⟩, ?_⟩
      · rw [← hs]
        exact hpar φ
      · rw [← hs, ← hc2, he]
    · rfl
  case hmain =>
    have hsumch : ∑ s ∈ TT, ∑ e' ∈ Ee, (chN s e' : ℝ) = ∑ φ, (α φ : ℝ) := by
      have h := sum_charge TT Ee c (fun φ => α φ) (fun φ hα => ⟨by rw [hc1]; exact (hsTT φ hα).1,
        by rw [hEe]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩)
      simp only [← hchN] at h
      exact_mod_cast h
    have hsumi : ∑ s ∈ TT, ∑ e' ∈ Ee, (iN s e' : ℝ) = ∑ k, (β k : ℝ) := by
      have h := sum_charge TT Ee (fun k : KapI ν r1 E => (k.1, k.2.1.val)) (fun k => β k)
        (fun k hk => ⟨hβTT k hk, by
          rw [hEe]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩)
      simp only [← hiN] at h
      exact_mod_cast h
    show gamP (p : ℝ) * ∑ s ∈ TT, (alN e s : ℝ) - ∑ s ∈ TT, ∑ e' ∈ Ee, (chN s e' : ℝ) -
      ∑ s ∈ TT, ∑ e' ∈ Ee, (iN s e' : ℝ) - deLoss p r0 r1 TT (alN e) (lsN l sf) ≤ _
    rw [hsumch, hsumi]
  case h6 =>
    intro s _ e' _
    show (chN s e' : ℝ) + (iN s e' : ℝ) ≤ (alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1)
    rw [le_div_iff₀ (pow_pos (by positivity) _)]
    have h := hlev s e'
    rw [mul_comm] at h
    exact_mod_cast h
  case h7 =>
    intro s _ e' _
    show (iN s e' : ℝ) ≤ min ((alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1))
      ((capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) : ℝ))
    apply le_min
    · rw [le_div_iff₀ (pow_pos (by positivity) _)]
      have h := hlev s e'
      have h' : iN s e' * p ^ (2 * e' + 1) ≤ alN e s := by
        rw [mul_comm]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) h
      exact_mod_cast h'
    · exact_mod_cast hcapN s e'
  refine le_trans hbound (Real.rpow_le_rpow_of_exponent_le hp1.le ?_)
  linarith [hcoreA]

end Formalism.InvariantFactorPaths.G7
