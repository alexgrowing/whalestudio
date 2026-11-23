import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.GrowthSums.StatementG

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace ParitySumsOverFilteredPairs

lemma sum_filter_fst {A B M : Type*} [Fintype A] [Fintype B] [DecidableEq A] [AddCommMonoid M]
    (S : Finset A) (f : A × B → M) :
    ∑ x ∈ univ.filter (fun x : A × B => x.1 ∈ S), f x = ∑ s ∈ S, ∑ y, f (s, y) := by
  have h : univ.filter (fun x : A × B => x.1 ∈ S) = S ×ˢ univ := by
    ext x
    simp
  rw [h, Finset.sum_product]

variable {ν r0 r1 E : ℕ}

lemma val_add_nat_mod_two [NeZero ν] (x : ZMod (2 * ν)) (m : ℕ) :
    (x + (m : ZMod (2 * ν))).val % 2 = (x.val + m) % 2 := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 ν), Nat.add_mod,
    Nat.mod_mod_of_dvd _ (dvd_mul_right 2 ν), ← Nat.add_mod]

lemma phi_parity [NeZero ν] (φ : PhiI ν r0 r1 E) :
    (pairSecond φ).val % 2 = ((pairFirst φ).val + 1) % 2 := by
  have hν : 1 ≤ 2 * ν := by have := NeZero.ne ν; omega
  have e : pairSecond φ = pairFirst φ +
      (((1 + 2 * φ.2.1.val + 2 * (φ.2.2.1.val * (2 * ν - 1))) : ℕ) : ZMod (2 * ν)) := by
    unfold pairFirst pairSecond
    have h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0 := ZMod.natCast_self _
    push_cast [Nat.cast_sub hν] at h0 ⊢
    linear_combination (-(2 * (φ.2.2.1.val : ZMod (2 * ν)))) * h0
  rw [e, val_add_nat_mod_two]
  omega

def iN (β : KapI ν r1 E →₀ ℕ) (s : ZMod (2 * ν)) (e' : ℕ) : ℕ :=
  if h : e' < E then ∑ b, β (s, ⟨e', h⟩, b) else 0

lemma iN_of_not_mem (β : KapI ν r1 E →₀ ℕ) (s : ZMod (2 * ν)) (e' : ℕ) (h : e' ∉ range E) :
    iN β s e' = 0 := by
  unfold iN
  rw [dif_neg (fun h' => h (Finset.mem_range.2 h'))]

lemma sum_iN [NeZero ν] (β : KapI ν r1 E →₀ ℕ) (A : Finset (ZMod (2 * ν))) :
    ∑ s ∈ A, ∑ e' ∈ range E, iN β s e' =
      ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1 ∈ A), β k := by
  rw [sum_filter_fst A (fun k => β k)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_range (fun e' => iN β s e'), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp [iN, e.isLt]

lemma one_le_dAof_left {p : ℕ} (hp : 0 < p) (φ : PhiI ν r0 r1 E) :
    1 ≤ dAof p φ (pairFirst φ, φ.2.2.2.2) := by
  unfold dAof
  rw [Finsupp.add_apply, Finsupp.single_eq_same]
  exact le_trans (Nat.one_le_pow (1 + 2 * φ.2.1.val) p hp) (Nat.le_add_right _ _)

lemma one_le_dAof_right {p : ℕ} (hp : 0 < p) (φ : PhiI ν r0 r1 E) :
    1 ≤ dAof p φ (pairSecond φ, φ.2.2.2.2) := by
  unfold dAof
  rw [Finsupp.add_apply, Finsupp.single_eq_same]
  exact le_trans (Nat.one_le_pow (2 * φ.2.2.1.val) p hp) (Nat.le_add_left _ _)

lemma pay_le [NeZero ν] {p : ℕ} (hp : 0 < p) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ) (P : Finset (TpV ν r1))
    (hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P ∨ (pairSecond φ, φ.2.2.2.2) ∈ P) :
    ∑ φ, α φ + ∑ k ∈ univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P), β k ≤
      ∑ τ ∈ P, e τ := by
  have hsum := Finset.sum_le_sum (fun τ (_ : τ ∈ P) => h3 τ)
  have e1 : ∑ τ ∈ P, ∑ φ, α φ * dAof p φ τ = ∑ φ, ∑ τ ∈ P, α φ * dAof p φ τ := Finset.sum_comm
  have e2 : ∑ τ ∈ P, ∑ k, β k * dBof p k τ = ∑ k, ∑ τ ∈ P, β k * dBof p k τ := Finset.sum_comm
  rw [Finset.sum_add_distrib, e1, e2] at hsum
  refine le_trans (add_le_add ?_ ?_) hsum
  · refine Finset.sum_le_sum (fun φ _ => ?_)
    rw [← Finset.mul_sum]
    by_cases hα : α φ = 0
    · simp [hα]
    · have h1 : 1 ≤ ∑ τ ∈ P, dAof p φ τ := by
        rcases hP φ hα with h | h
        · exact le_trans (one_le_dAof_left hp φ) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h)
        · exact le_trans (one_le_dAof_right hp φ) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h)
      calc α φ = α φ * 1 := (mul_one _).symm
        _ ≤ α φ * ∑ τ ∈ P, dAof p φ τ := Nat.mul_le_mul_left _ h1
  · rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun k _ => ?_)
    split_ifs with hk
    · rw [← Finset.mul_sum]
      have h1 : 1 ≤ ∑ τ ∈ P, dBof p k τ := by
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk)
        simp only [dBof, Finsupp.single_eq_same]
        exact Nat.one_le_pow _ _ hp
      calc β k = β k * 1 := (mul_one _).symm
        _ ≤ β k * ∑ τ ∈ P, dBof p k τ := Nat.mul_le_mul_left _ h1
    · exact Nat.zero_le _

lemma iN_mul_le [NeZero ν] {p : ℕ} (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ) (s : ZMod (2 * ν)) (e' : ℕ) :
    iN β s e' * p ^ (2 * e' + 1) ≤ alN e s := by
  unfold iN alN
  split_ifs with h
  · rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun b _ => ?_)
    have h1 := h3 (s, b)
    have h2 : β (s, ⟨e', h⟩, b) * dBof p (s, ⟨e', h⟩, b) (s, b) ≤ ∑ k, β k * dBof p k (s, b) :=
      Finset.single_le_sum (f := fun k => β k * dBof p k (s, b)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)
    have h4 : dBof p (s, ⟨e', h⟩, b) (s, b) = p ^ (2 * e' + 1) := by
      simp [dBof]
    rw [h4] at h2
    exact le_trans h2 (le_trans (Nat.le_add_left _ _) h1)
  · simp

lemma iN_le_cap (hC : HitsCapPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} (p : ℕ)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (β : KapI ν r1 E →₀ ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (s : ZMod (2 * ν)) (e' : ℕ) :
    iN β s e' ≤ capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) := by
  unfold iN
  split_ifs with h
  · by_contra hlt
    push_neg at hlt
    apply h4
    exact hC K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I
      (fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν)))
      (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
      ((univ : Finset (Fin r1)).image (fun b => (s, (⟨e', h⟩ : Fin E), b)))
      (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν)))
      (fun k hk => by obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hk; rfl)
      (fun k hk k' hk' => by
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hk
        obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 hk'
        rfl)
      β
      (by
        rw [Finset.sum_image (fun b _ b' _ hbb => by simpa using hbb)]
        exact hlt)
  · exact Nat.zero_le _

lemma iN_le_min (hC : HitsCapPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} {p : ℕ} (hp : 0 < p)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (s : ZMod (2 * ν)) (e' : ℕ) :
    (iN β s e' : ℝ) ≤ min ((alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1))
      (capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) : ℝ) := by
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (pow_pos (Nat.cast_pos.2 hp) _)]
    exact_mod_cast iN_mul_le α β e h3 s e'
  · exact_mod_cast iN_le_cap hC p ξ β l sf T I h4 s e'

lemma sum_iN_tops [NeZero ν] (β : KapI ν r1 E →₀ ℕ) (TT : Finset (ZMod (2 * ν)))
    (h2 : ∀ k, β k ≠ 0 → k.1 ∈ TT) :
    ∑ s ∈ TT, ∑ e' ∈ range E, iN β s e' = ∑ k, β k := by
  rw [sum_iN β TT]
  exact Finset.sum_filter_of_ne (fun k _ hk => h2 k hk)

lemma low_pay (hJ : HitsColumnsPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} (p : ℕ)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (β : KapI ν r1 E →₀ ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (J : Finset (Fin r1)) :
    ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J), β k ≤
      ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0) := by
  classical
  set Od : Finset (ZMod (2 * ν)) := univ.filter (fun s => s.val % 2 = 1) with hOd
  set pos : KapI ν r1 E → ZMod (2 * ν) := fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν))
    with hpos
  have hmaps : ∀ k ∈ univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J), pos k ∈ Od := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hOd, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [hpos]
    rw [val_add_nat_mod_two]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hR : ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0) =
      ∑ y ∈ Od, ∑ c ∈ univ.filter (fun c => sf c = y), ((univ.image (I c)) ∩ J).card := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (g := sf) (t := Od) (fun c hc => by
      rw [Finset.mem_filter] at hc
      rw [hOd, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hc.2⟩)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [hOd, Finset.mem_filter] at hy
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; exact hy.2, h⟩
  rw [hR]
  refine Finset.sum_le_sum (fun y _ => ?_)
  by_contra hlt
  push_neg at hlt
  apply h4
  exact hJ K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I pos
    (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
    ((univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J)).filter (fun k => pos k = y)) y J
    (fun k hk => (Finset.mem_filter.1 hk).2)
    (fun k hk => ((Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2).2) β hlt

end ParitySumsOverFilteredPairs

open ParitySumsOverFilteredPairs

theorem entryCappedBound_of (hS : EntryStar) (hC : HitsCapPos) (hA : Formalism.GrowthSums.CappedGainSubLE) : EntryCappedBound := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hH
  have hH' := hH
  obtain ⟨-, hp2, -, -, -, -, -, -⟩ := hH'
  have hp : 0 < p := by omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hH with h0 | ⟨E, α, β, hα, hβ, h3, h4, hn⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · refine le_trans hn (Real.rpow_le_rpow_of_exponent_le hp1.le ?_)
    set P2 : Finset (TpV ν r1) := univ.filter (fun x : TpV ν r1 => x.1 ∈ TT \ oddT TT) with hP2def
    have hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P2 ∨ (pairSecond φ, φ.2.2.2.2) ∈ P2 := by
      intro φ hφ
      obtain ⟨h1, h2⟩ := hα φ hφ
      have hpar := phi_parity φ
      simp only [hP2def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, oddT, not_and]
      by_cases hv : (pairFirst φ).val % 2 = 1
      · right
        exact ⟨h2, fun _ => by show ¬ (pairSecond φ).val % 2 = 1; omega⟩
      · left
        exact ⟨h1, fun _ => hv⟩
    have key : ∑ φ, α φ + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, iN β s e' ≤
        ∑ s ∈ TT \ oddT TT, alN e s := by
      rw [sum_iN β (TT \ oddT TT)]
      have hfil : univ.filter (fun k : KapI ν r1 E => k.1 ∈ TT \ oddT TT) =
          univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P2) := by
        ext k
        simp [hP2def]
      rw [hfil]
      refine le_trans (pay_le hp α β e h3 P2 hP) (le_of_eq ?_)
      exact sum_filter_fst (A := ZMod (2 * ν)) (B := Fin r1) (TT \ oddT TT) e
    have hsumβ : ∑ s ∈ TT, ∑ e' ∈ range E, (iN β s e' : ℝ) = ∑ k, (β k : ℝ) := by
      exact_mod_cast sum_iN_tops β TT hβ
    have keyR : ∑ φ, (α φ : ℝ) + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, (iN β s e' : ℝ) ≤
        ∑ s ∈ TT \ oddT TT, (alN e s : ℝ) := by
      exact_mod_cast key
    have core := hA (2 * ν) (p : ℝ) TT (oddT TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
      (deLoss p r0 r1 TT (alN e) (lsN l sf))
      (gamP p * ∑ s ∈ TT, (alN e s : ℝ) - ∑ φ, (α φ : ℝ) - ∑ k, (β k : ℝ) -
        deLoss p r0 r1 TT (alN e) (lsN l sf))
      (∑ φ, (α φ : ℝ)) (fun s e' => (iN β s e' : ℝ)) (range E)
      hp1 (Finset.filter_subset _ _) (fun s => Nat.cast_nonneg _) (fun s => Nat.cast_nonneg _)
      (fun s e' => Nat.cast_nonneg _) (fun s e' he => by simp [iN_of_not_mem β s e' he])
      (by beta_reduce; linarith [hsumβ]) (by beta_reduce; exact keyR)
      (fun s _ e' => iN_le_min hC hp ξ α β e l sf T I h3 h4 s e')
    beta_reduce at core
    linarith [core]

theorem EntryB_of (hS : EntryStar) (hC : HitsCapPos) (hJ : HitsColumnsPos) (hB : BCore) :
    EntryB := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I J hH
  have hH' := hH
  obtain ⟨-, hp2, hpn, -, -, -, -, -⟩ := hH'
  have hp : 0 < p := by omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  set N := ∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
          then e x else 0) +
        ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I c)) ∩ J).card else 0) with hN
  rw [norm_mul, norm_pow, hpn]
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hH with h0 | ⟨E, α, β, hα, hβ, h3, h4, hn⟩
  · rw [h0, norm_zero, mul_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · have hpinv : ((p : ℝ)⁻¹) ^ N = (p : ℝ) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_natCast, inv_pow]
    rw [hpinv]
    refine le_trans (mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (Nat.cast_nonneg p) _)) ?_
    rw [← Real.rpow_add (by exact_mod_cast hp)]
    refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
    set P : Finset (TpV ν r1) := univ.filter (fun x : TpV ν r1 =>
      (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)) with hPdef
    have hP : ∀ φ, α φ ≠ 0 → (pairFirst φ, φ.2.2.2.2) ∈ P ∨ (pairSecond φ, φ.2.2.2.2) ∈ P := by
      intro φ _
      have hpar := phi_parity φ
      simp only [hPdef, Finset.mem_filter, Finset.mem_univ, true_and]
      show ((pairFirst φ).val % 2 = 0 ∧ φ.2.2.2.2 ∉ J ∨ (pairFirst φ).val % 2 = 1 ∧ φ.2.2.2.2 ∈ J) ∨
        ((pairSecond φ).val % 2 = 0 ∧ φ.2.2.2.2 ∉ J ∨ (pairSecond φ).val % 2 = 1 ∧ φ.2.2.2.2 ∈ J)
      by_cases hb : φ.2.2.2.2 ∈ J
      · by_cases hv : (pairFirst φ).val % 2 = 1
        · exact Or.inl (Or.inr ⟨hv, hb⟩)
        · exact Or.inr (Or.inr ⟨by omega, hb⟩)
      · by_cases hv : (pairFirst φ).val % 2 = 0
        · exact Or.inl (Or.inl ⟨hv, hb⟩)
        · exact Or.inr (Or.inl ⟨by omega, hb⟩)
    have keyB : ∑ φ, α φ + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, iN β s e' ≤ N := by
      rw [sum_iN β (TT \ oddT TT)]
      have hpay := pay_le hp α β e h3 P hP
      have hlow := low_pay hJ p ξ β l sf T I h4 J
      have hNe : ∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
          then e x else 0) = ∑ τ ∈ P, e τ := by
        rw [hPdef, Finset.sum_filter]
      have hsplit : ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1 ∈ TT \ oddT TT), β k ≤
          ∑ k ∈ univ.filter (fun k : KapI ν r1 E => (k.1, k.2.2) ∈ P), β k +
          ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1.val % 2 = 0 ∧ k.2.2 ∈ J), β k := by
        simp only [Finset.sum_filter]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun k _ => ?_)
        by_cases h1 : k.1 ∈ TT \ oddT TT
        · have hev : k.1.val % 2 = 0 := by
            simp only [oddT, Finset.mem_sdiff, Finset.mem_filter, not_and] at h1
            have := h1.2 h1.1
            omega
          rw [if_pos h1]
          by_cases hb : k.2.2 ∈ J
          · rw [if_pos (show k.1.val % 2 = 0 ∧ k.2.2 ∈ J from ⟨hev, hb⟩)]
            exact Nat.le_add_left _ _
          · rw [if_pos (show (k.1, k.2.2) ∈ P by simp [hPdef, hev, hb])]
            exact Nat.le_add_right _ _
        · rw [if_neg h1]
          exact Nat.zero_le _
      rw [hN]
      omega
    have hsumβ : ∑ s ∈ TT, ∑ e' ∈ range E, (iN β s e' : ℝ) = ∑ k, (β k : ℝ) := by
      exact_mod_cast sum_iN_tops β TT hβ
    have keyR : ∑ φ, (α φ : ℝ) + ∑ s ∈ TT \ oddT TT, ∑ e' ∈ range E, (iN β s e' : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast keyB
    have core := hB (2 * ν) (p : ℝ) TT (oddT TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
      (deLoss p r0 r1 TT (alN e) (lsN l sf))
      ((N : ℝ) + gamP p * ∑ s ∈ TT, (alN e s : ℝ) - ∑ φ, (α φ : ℝ) - ∑ k, (β k : ℝ) -
        deLoss p r0 r1 TT (alN e) (lsN l sf))
      ((N : ℝ) - ∑ φ, (α φ : ℝ)) (fun s e' => (iN β s e' : ℝ)) (range E)
      hp1 (Finset.filter_subset _ _) (fun s => Nat.cast_nonneg _) (fun s => Nat.cast_nonneg _)
      (fun s e' => Nat.cast_nonneg _) (fun s e' he => by simp [iN_of_not_mem β s e' he])
      (by beta_reduce; linarith [hsumβ]) (by beta_reduce; linarith [keyR])
      (fun s _ e' => iN_le_min hC hp ξ α β e l sf T I h3 h4 s e')
    beta_reduce at core
    linarith [core]

end Formalism.InvariantFactorPaths.G7
