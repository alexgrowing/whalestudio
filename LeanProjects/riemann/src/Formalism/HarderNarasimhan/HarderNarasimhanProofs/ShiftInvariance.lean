import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

open Module Submodule

noncomputable section

namespace Formalism.HN

universe u v w w₂

theorem shiftInv_zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  exact satBasic_zl_mono ρ h

theorem shiftInv_isSat_iff {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    {L : Submodule R V} (hL : IsLat ρ L) (N : Submodule R V) :
    IsSat ρ L N ↔
      N ≤ L ∧ ∀ N' : Submodule R V, N ≤ N' → N' ≤ L → rk ρ N' = rk ρ N → N' = N := by
  have hB := saturation_basic_properties R V E ρ L hL
  constructor
  · intro hN
    exact ⟨hN.1, fun N' h₁ h₂ h₃ => hB.2.2.1 N N' hN h₁ h₂ h₃⟩
  · rintro ⟨hNL, hmax⟩
    obtain ⟨N', hNN', hN'L, himg⟩ := real_saturation_property R V E ρ L N hL hNL
    have hsat := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hL.2
      (shiftInv_zl_mono ρ hNL)
    have hrk : rk ρ N' = rk ρ N := by
      show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
      rw [himg]
      exact hsat.2.2
    have heq : N' = N := hmax N' hNN' hN'L hrk
    refine ⟨hNL, ?_⟩
    rw [← heq, himg]
    exact hsat.1

theorem shiftInv_mu {R : Type u} {V : Type v} {E : Type w} {E₂ : Type w₂} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [FiniteDimensional ℝ E₂] (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (ρ : V →+ E) (ρ₂ : V →+ E₂) (L : Submodule R V) (c : ℝ) (hL : IsLat ρ L)
    (hL₂ : IsLat ρ₂ L)
    (hsh : ∀ N : Submodule R V, N ≤ L → rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N + c * rk ρ N)
    (hL0 : L ≠ ⊥) : muMax ρ₂ L = muMax ρ L + c ∧ muMin ρ₂ L = muMin ρ L + c := by
  obtain ⟨hmax, hmin, -, -, -⟩ := h1 R V E ρ L hL hL0
  obtain ⟨hmax₂, hmin₂, -, -, -⟩ := h1' R V E₂ ρ₂ L hL₂ hL0
  have hrL := (hsh L le_rfl).1
  have hdL := (hsh L le_rfl).2
  constructor
  · apply le_antisymm
    · rw [hmax₂]
      intro N hN
      rw [(hsh N hN).1, (hsh N hN).2]
      have := (hmax (muMax ρ L)).1 le_rfl N hN
      linarith
    · have key : muMax ρ L ≤ muMax ρ₂ L - c := by
        rw [hmax]
        intro N hN
        have := (hmax₂ (muMax ρ₂ L)).1 le_rfl N hN
        rw [(hsh N hN).1, (hsh N hN).2] at this
        linarith
      linarith
  · apply le_antisymm
    · have key : muMin ρ₂ L - c ≤ muMin ρ L := by
        rw [hmin]
        intro N hN
        have := (hmin₂ (muMin ρ₂ L)).1 le_rfl N hN
        rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2] at this
        linarith
      linarith
    · rw [hmin₂]
      intro N hN
      rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2]
      have := (hmin (muMin ρ L)).1 le_rfl N hN
      linarith

theorem shiftInv_count (c : ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, if i < k then c else 0) = c * ((min k m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < k
    · rw [if_pos h, min_eq_right h.le, min_eq_right (show m + 1 ≤ k by omega)]
      push_cast
      ring
    · rw [if_neg h]
      replace h := not_lt.mp h
      rw [min_eq_left h, min_eq_left (show k ≤ m + 1 by omega)]
      ring

private theorem sum_fin_ite_lt_const_eq_mul_min (c : ℝ) (k n : ℕ) :
    (∑ j : Fin n, if (j : ℕ) < k then c else 0) = c * ((min k n : ℕ) : ℝ) :=
  (Fin.sum_univ_eq_sum_range (fun i => if i < k then c else 0) n).trans (shiftInv_count c k n)

theorem shiftInv_sum {n m : ℕ} (h : m = n) (f : Fin n → ℝ) (g : Fin m → ℝ) (c : ℝ) (k : ℕ)
    (hfg : ∀ (j : ℕ) (h1 : j < m) (h2 : j < n), g ⟨j, h1⟩ = f ⟨j, h2⟩ + c) :
    (∑ j : Fin m, if (j : ℕ) < k then g j else 0) =
      (∑ j : Fin n, if (j : ℕ) < k then f j else 0) + c * ((min k n : ℕ) : ℝ) := by
  subst h
  rw [← sum_fin_ite_lt_const_eq_mul_min c k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact hfg j.1 j.2 j.2
  · simp

private theorem lt_card_filter_le_iff_of_antitone {n : ℕ} {s : Fin n → ℝ} (hs : Antitone s) (j : Fin n) (θ : ℝ) :
    (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ s i)).card ↔ θ ≤ s j := by
  constructor
  · intro h
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h2 : Finset.univ.filter (fun i => θ ≤ s i) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hji
      replace hji := not_lt.mp hji
      have := hs hji
      linarith
    have c2 := Finset.card_le_card h2
    rw [Fin.card_Iio] at c2
    omega
  · intro h
    have h1 : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ s i) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hs hi)
    have c1 := Finset.card_le_card h1
    rw [Fin.card_Iic] at c1
    omega

theorem shiftInvariance_of (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (h4 : HNSlopes.{u, v, w}) : ShiftInvariance.{u, v, w, w₂} := by
  intro R V E E₂ _ _ _ _ _ _ _ _ _ ρ ρ₂ L c hL hL₂ hsh
  have hBL := saturation_basic_properties R V E ρ L hL
  have hBL₂ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have hfilt : ∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ := by
    intro θ
    unfold hnStep
    congr 1
    ext N
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
  have hfiltle : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => sSup_le fun N hN => hN.1
  have hS := h4 R V E ρ L hL
  have hslope : ∀ (j : ℕ) (hj₂ : j < rk ρ₂ L) (hj : j < rk ρ L),
      slopeList ρ₂ L ⟨j, hj₂⟩ = slopeList ρ L ⟨j, hj⟩ + c := by
    intro j hj₂ hj
    have hset : {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = Set.Iic (slopeList ρ L ⟨j, hj⟩ + c) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      have hf : hnStep ρ₂ L θ = hnStep ρ L (θ - c) := by
        have := hfilt (θ - c)
        rwa [sub_add_cancel] at this
      rw [hf, (hsh _ (hfiltle (θ - c))).1, ← hS.2.1 (θ - c)]
      refine (lt_card_filter_le_iff_of_antitone hS.1 ⟨j, hj⟩ (θ - c)).trans ?_
      constructor <;> intro h <;> linarith
    show sSup {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = slopeList ρ L ⟨j, hj⟩ + c
    rw [hset, csSup_Iic]
  refine ⟨fun N => ?_, fun hL0 => shiftInv_mu h1 h1' ρ ρ₂ L c hL hL₂ hsh hL0,
    hfilt, fun k => ?_⟩
  · rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1]
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1] at hr
  · exact shiftInv_sum (hsh L le_rfl).1 (slopeList ρ L) (slopeList ρ₂ L) c k hslope

end Formalism.HN
