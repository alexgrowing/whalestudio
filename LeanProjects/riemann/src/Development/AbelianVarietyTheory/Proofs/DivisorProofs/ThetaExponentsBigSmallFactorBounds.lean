import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSpread IsSmall sumSmallSpread)
open GlobalTheory.AllWt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.ThetaExp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical

theorem thA_big (u : Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thA Dw u n (τ.1, i) = (u τ ⟨i, by omega⟩ - u τ ⟨Dw.p - 1, by omega⟩ + 1).toNat := by
  simp only [thA, wtOf_big _ _ τ i hi, shift, dif_pos (show 0 < Dw.p by omega), Pi.add_apply, GlobalTheory.FlatLine.parWt]
  congr 1; ring

theorem thA_small (u : Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) (hp : 0 < Dw.p) :
    thA Dw u n (conjEmb τ.1, i) =
      (u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 1 - 2 * ((n / 2 : ℕ) : ℤ)).toNat := by
  simp only [thA, wtOf_small _ _ τ i hi, shift, dif_pos hp, Pi.add_apply, GlobalTheory.FlatLine.parWt]
  congr 1; ring

theorem thA_out (u : Weight Dw) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) (h : Dw.mult τ ≤ i) : thA Dw u n (τ, i) = 0 := by
  unfold Datum.mult at h
  simp only [thA, wtOf]
  split_ifs at h ⊢ <;> first | omega | simp

theorem psi_or_conj (τ : E →+* ℂ) : (∃ τ' : Psi H, τ = τ'.1) ∨ ∃ τ' : Psi H, τ = conjEmb τ'.1 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨τ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, (conjEmb_conjEmb τ).symm⟩

theorem mult_psi (τ : Psi H) : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]

theorem mult_conj (τ : Psi H) : Dw.mult (conjEmb τ.1) = Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]

theorem tele_real (f : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.range K, ((j : ℝ) + 1) * (f j - f (j + 1)) = ∑ j ∈ Finset.range K, (f j - f K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

theorem thA_anti (u : Weight Dw) (n : ℕ) (hanti : ∀ τ, Antitone (u τ)) (hp : 0 < Dw.p) (τ : E →+* ℂ) :
    Antitone fun i => thA Dw u n (τ, i) := by
  apply antitone_nat_of_succ_le
  intro i
  by_cases hm : Dw.mult τ ≤ i + 1
  · simp only [thA_out u n τ (i + 1) hm]; exact Nat.zero_le _
  rcases psi_or_conj (H := H) τ with ⟨τ', rfl⟩ | ⟨τ', rfl⟩
  · rw [mult_psi] at hm
    simp only [thA_big u n τ' (i + 1) (by omega), thA_big u n τ' i (by omega)]
    apply Int.toNat_le_toNat
    have := hanti τ' (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
    linarith
  · rw [mult_conj] at hm
    simp only [thA_small u n τ' (i + 1) (by omega) hp, thA_small u n τ' i (by omega) hp]
    apply Int.toNat_le_toNat
    have := hanti τ' (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
      ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
    linarith

theorem thA_le (u : Weight Dw) (n B : ℕ) (hB : ∀ τ i, |u τ i| ≤ B) (hp : 0 < Dw.p) (x : (E →+* ℂ) × ℕ) :
    thA Dw u n x ≤ 2 * B + 1 := by
  obtain ⟨τ, i⟩ := x
  by_cases hm : Dw.mult τ ≤ i
  · rw [thA_out u n τ i hm]; omega
  rcases psi_or_conj (H := H) τ with ⟨τ', rfl⟩ | ⟨τ', rfl⟩
  · rw [mult_psi] at hm
    rw [thA_big u n τ' i (by omega), Int.toNat_le]
    have h1 := abs_le.1 (hB τ' ⟨i, by omega⟩)
    have h2 := abs_le.1 (hB τ' ⟨Dw.p - 1, by omega⟩)
    push_cast; linarith
  · rw [mult_conj] at hm
    rw [thA_small u n τ' i (by omega) hp, Int.toNat_le]
    have h1 := abs_le.1 (hB τ' ⟨Dw.p + (Dw.q - 1 - i), by omega⟩)
    have h2 := abs_le.1 (hB τ' ⟨Dw.p - 1, by omega⟩)
    omega

theorem thA_le_conj (u : Weight Dw) (n B : ℕ) (hB : ∀ τ i, |u τ i| ≤ B) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) :
    thA Dw u n (conjEmb τ.1, i) ≤ 2 * B := by
  by_cases hm : Dw.mult (conjEmb τ.1) ≤ i
  · rw [thA_out u n _ i hm]; omega
  rw [mult_conj] at hm
  rw [thA_small u n τ i (by omega) hp, Int.toNat_le]
  have h1 := abs_le.1 (hB τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩)
  have h2 := abs_le.1 (hB τ ⟨Dw.p - 1, by omega⟩)
  omega

theorem sum_lieFactorRank_mul_exponentGap_eq (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (ha : Antitone fun i => a (τ, i))
    (hm : a (τ, Dw.mult τ) = 0) (K : ℕ) (hK : K ≤ Dw.mult τ) :
    ∑ j : Fin (Dw.mult τ), (if (j : ℕ) < K then ((rk (⟨τ, j⟩ : Lt1 Dw) * gap Dw a ⟨τ, j⟩ : ℕ) : ℝ) else 0) =
      ∑ j ∈ Finset.range K, ((a (τ, j) : ℝ) - a (τ, K)) := by
  rw [← tele_real (fun j => (a (τ, j) : ℝ)) K]
  have step : ∀ j : Fin (Dw.mult τ),
      (if (j : ℕ) < K then ((rk (⟨τ, j⟩ : Lt1 Dw) * gap Dw a ⟨τ, j⟩ : ℕ) : ℝ) else 0) =
        (fun j : ℕ => if j < K then ((j : ℝ) + 1) * ((a (τ, j) : ℝ) - a (τ, j + 1)) else 0) (j : ℕ) := by
    intro j
    simp only []
    split_ifs with hj
    · have hg : gap Dw a ⟨τ, j⟩ = a (τ, j) - a (τ, (j : ℕ) + 1) := by
        unfold gap
        simp only [rk]
        split_ifs with h
        · rfl
        · have e : (j : ℕ) + 1 = Dw.mult τ := by omega
          rw [e, hm]
      rw [hg, Nat.cast_mul, Nat.cast_sub (ha (Nat.le_succ _))]
      simp only [rk]; push_cast; ring
    · rfl
  rw [Finset.sum_congr rfl (fun j _ => step j),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < K then ((j : ℝ) + 1) * ((a (τ, j) : ℝ) - a (τ, j + 1)) else 0),
    ← Finset.sum_filter]
  congr 1
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem card_psi (F : ℕ) (hF : Module.finrank ℚ E = 2 * F) :
    (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = F ∧
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = F := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card =
      (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card := by
    apply Finset.card_bij (fun τ _ => conjEmb τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact conj_mem hτ
    · intro a _ b _ h
      rw [← conjEmb_conjEmb a, h, conjEmb_conjEmb]
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨conjEmb b, by simpa using conj_not_mem (H := H) ⟨b, hb⟩, conjEmb_conjEmb b⟩
  have ht := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, NumberField.Embeddings.card E ℂ, hF] at ht
  omega

open Classical in

theorem big_le (u : Weight Dw) (k n B : ℕ) (hk : 2 ≤ k) (hkp : k ≤ Dw.p + 1) (hanti : ∀ τ, Antitone (u τ))
    (hz : ∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) (hB : ∀ τ i, |u τ i| ≤ B) (τ : E →+* ℂ) :
    ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), gap Dw (thA Dw u n) f ≤ B + 1 := by
  have hp : 0 < Dw.p := by omega
  by_cases h : InPsi H τ
  · obtain ⟨τ', rfl⟩ : ∃ τ' : Psi H, τ = τ'.1 := ⟨⟨τ, h⟩, rfl⟩
    have hlt : k - 2 < Dw.mult τ'.1 := by rw [mult_psi]; omega
    have e := sum_gap_row (Dw := Dw) (thA_anti u n hanti hp) τ'.1 ⟨k - 2, hlt⟩
    have e2 : Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ'.1) =
        Finset.univ.filter (fun f : Lt1 Dw => f.1 = τ'.1 ∧ k - 2 < rk f) := by
      refine Finset.filter_congr fun f _ => ?_
      unfold IsBig
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, by omega⟩
      · rintro ⟨h3, h2⟩
        exact ⟨⟨h3 ▸ h, by omega⟩, h3⟩
    rw [e2]
    refine le_of_eq_of_le (by convert e) ?_
    show thA Dw u n (τ'.1, k - 2) ≤ B + 1
    rw [thA_big u n τ' (k - 2) (by omega), hz τ' ⟨k - 2, by omega⟩ (by show k - 2 + 2 = k; omega), Int.toNat_le]
    have h2 := abs_le.1 (hB τ' ⟨Dw.p - 1, by omega⟩)
    omega
  · rw [Finset.sum_eq_zero]
    · omega
    · intro f hf
      have hf' := (Finset.mem_filter.1 hf).2
      exact absurd (hf'.2 ▸ hf'.1.1) h

theorem cloud_eq (u : Weight Dw) (k n : ℕ) (hk : 2 ≤ k) (hkp : k ≤ Dw.p + 1) (hanti : ∀ τ, Antitone (u τ))
    (hz : ∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) (τ : Psi H) :
    ∑ j ∈ Finset.range (k - 2), ((thA Dw u n (τ.1, j) : ℝ) - thA Dw u n (τ.1, k - 2)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Dw.p + Dw.q) => (i : ℕ) + 2 < k), (u τ i : ℝ) := by
  have val : ∀ i (hi : i < Dw.p), (thA Dw u n (τ.1, i) : ℝ) =
      (u τ ⟨i, by omega⟩ : ℝ) - (u τ ⟨Dw.p - 1, by omega⟩ : ℝ) + 1 := by
    intro i hi
    have h := hanti τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
    have h2 : ((thA Dw u n (τ.1, i) : ℕ) : ℤ) = u τ ⟨i, by omega⟩ - u τ ⟨Dw.p - 1, by omega⟩ + 1 := by
      rw [thA_big u n τ i hi, Int.toNat_of_nonneg (by omega)]
    exact_mod_cast h2
  symm
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    have := (Finset.mem_filter.1 hi).2
    exact Finset.mem_range.2 (by omega)
  · intro i _ j _ h
    exact Fin.ext h
  · intro j hj
    have := Finset.mem_range.1 hj
    exact ⟨⟨j, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by show j + 2 < k; omega⟩, rfl⟩
  · intro i hi
    have := (Finset.mem_filter.1 hi).2
    rw [val i (by omega), val (k - 2) (by omega), hz τ ⟨k - 2, by omega⟩ (by show k - 2 + 2 = k; omega)]
    simp

open Classical in

theorem row_le (u : Weight Dw) (k n B : ℕ) (Sg : ℝ) (hk : 2 ≤ k) (hkp : k ≤ Dw.p + 1) (hu : WtBd Dw k n u B Sg)
    (τ : E →+* ℂ) :
    ∑ j : Fin (Dw.mult τ), (if IsSmall (⟨τ, j⟩ : Lt1 Dw) ∨ IsSpread k (⟨τ, j⟩ : Lt1 Dw) then
      ((rk (⟨τ, j⟩ : Lt1 Dw) * gap Dw (thA Dw u n) ⟨τ, j⟩ : ℕ) : ℝ) else 0) ≤
      if τ (H.rt : E) = H.rt0 then Sg else 2 * (Dw.q : ℝ) * B := by
  obtain ⟨hanti, hz, -, hB, hS⟩ := hu
  have hp : 0 < Dw.p := by omega
  have key := sum_lieFactorRank_mul_exponentGap_eq (Dw := Dw) (thA Dw u n) τ (thA_anti u n hanti hp τ) (thA_out u n τ _ le_rfl)
  rcases psi_or_conj (H := H) τ with ⟨τ', rfl⟩ | ⟨τ', rfl⟩
  · rw [if_pos τ'.2]
    refine le_of_eq_of_le ?_ (hS τ')
    rw [← cloud_eq u k n hk hkp hanti hz τ', ← key (k - 2) (by rw [mult_psi]; omega)]
    refine Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
    have h : InPsi H τ'.1 := τ'.2
    simp only [IsSmall, IsSpread, h, not_true, false_or, true_and, rk]
    omega
  · rw [if_neg (conj_not_mem τ')]
    have h : ¬ InPsi H (conjEmb τ'.1) := conj_not_mem τ'
    have key2 := key _ le_rfl
    simp only [Fin.is_lt, if_true, thA_out u n _ _ le_rfl] at key2
    simp only [IsSmall, h, not_false_iff, true_or, if_true]
    rw [key2, mult_conj]
    calc _ ≤ ∑ j ∈ Finset.range Dw.q, (2 * (B : ℝ)) := Finset.sum_le_sum fun j _ => by
          have : ((thA Dw u n (conjEmb τ'.1, j) : ℕ) : ℝ) ≤ ((2 * B : ℕ) : ℝ) :=
            Nat.cast_le.2 (thA_le_conj u n B hB hp τ' j)
          push_cast at this ⊢; linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem expBd_thA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), ∀ (F k m n B : ℕ) (Sg : ℝ) (u : GlobalTheory.AllWt.Weight Dw), Shape Dw F k m → k ≤ Dw.p + 1 → WtBd Dw k n u B Sg → ExpBd Dw k (gap Dw (thA Dw u n)) (B + 1) (F * (Sg + 2 * Dw.q * B)) (2 * B + 1) := by
  intro E _ _ _ H Dw F k m n B Sg u hsh hkp hu
  obtain ⟨-, -, -, -, hk, hF⟩ := hsh
  have hp : 0 < Dw.p := by omega
  refine ⟨by positivity, fun τ => ?_, ?_, fun f => ?_⟩
  · exact_mod_cast big_le u k n B hk hkp hu.1 hu.2.1 hu.2.2.2.1 τ
  · unfold sumSmallSpread
    rw [Finset.sum_filter, Fintype.sum_sigma, Nat.cast_sum]
    calc _ ≤ ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then Sg else 2 * (Dw.q : ℝ) * B) :=
          Finset.sum_le_sum fun τ _ => by
            refine le_of_eq_of_le ?_ (row_le u k n B Sg hk hkp hu τ)
            rw [Nat.cast_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp
      _ = _ := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, (card_psi F hF).1, (card_psi F hF).2]
          simp only [nsmul_eq_mul]; ring
  · exact (Nat.sub_le _ _).trans (thA_le u n B hu.2.2.2.1 hp _)

end GlobalTheory.RefSum.ThetaExp

end
