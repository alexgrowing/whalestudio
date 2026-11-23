import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsModulePieceHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulePieceHilbertChain
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem not_horizontal_of_mem {W : Ideal (MRing ι)} {N : ℕ} (hN : N ≠ 0) (hNW : (N : MRing ι) ∈ W) :
    ¬ IsHorizontal W := by
  intro h
  have : (N : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hNW
  rw [IsHorizontal] at h
  rw [h, Ideal.mem_bot] at this
  exact hN (by exact_mod_cast this)

theorem not_horizontal_of_charOf {W : Ideal (MRing ι)} (hc : charOf W ≠ 0) : ¬ IsHorizontal W := by
  intro h
  apply hc
  rw [charOf, (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h, Int.natAbs_zero]

theorem geoNum_cut_X [DecidableEq K] : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K)
    (i : ι k), IsMultiProjPrime V → charOf V ≠ 0 →
    ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (X ⟨k, i⟩ : MRing ι) ∉ V →
    (a (Fin.last n) = fun k' => if k' = k then 1 else 0) →
    geoNum (n + 1) V a = ∑ᶠ W' ∈ divSupp V (X ⟨k, i⟩),
      (multAt (V ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum n W' (Fin.init a) := by
  intro n V a k i hV hc hdim hX ha
  have hp := charOf_prime hV.1 (not_horizontal_of_charOf hc)
  have h := Inter.GeoNumCut.full K ι V n (Fin.init a) (Pi.single k 1) (X ⟨k, i⟩) hV hp hdim
    (isMultiHomog_X' k i) hX
  have e : (fun k' => (((Pi.single k 1 : K → ℕ) k' : ℕ) : ℤ)) = a (Fin.last n) := by
    rw [ha]
    funext k'
    by_cases hk : k' = k
    · subst hk
      simp
    · simp [hk]
  rw [e, Fin.snoc_init_self] at h
  exact h

theorem geoNum_symm [DecidableEq K] : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ)
    (σ : Equiv.Perm (Fin n)), IsMultiProjPrime V → charOf V ≠ 0 →
    ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
    geoNum n V (a ∘ σ) = geoNum n V a := by
  intro n V a σ hV hc hdim
  have : Fact (charOf V).Prime := ⟨charOf_prime hV.1 (not_horizontal_of_charOf hc)⟩
  rw [← Bridge.intNum_map_eq_geoNum (charOf V) n V hV (Inter.C_charOf_mem V) hdim,
    ← Bridge.intNum_map_eq_geoNum (charOf V) n V hV (Inter.C_charOf_mem V) hdim]
  exact FieldNumbers.IntNumSymm.full (ZMod (charOf V)) K ι _ n a σ

theorem exists_dim_nat [DecidableEq K] {q : Ideal (MRing ι)} (hq : q.IsPrime) (hqm : IsMultiHomogIdeal q)
    (hrel : IsRelevant q) {d : ℕ}
    (hd : ringKrullDim (MRing ι ⧸ q) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ d' ≤ d, ringKrullDim (MRing ι ⧸ q) = ((d' + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have h1 := card_le_dim hq hqm hrel
  generalize ringKrullDim (MRing ι ⧸ q) = x at h1 hd ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have := WithBot.coe_le_coe.1 hd
      exact absurd (top_le_iff.1 this) (ENat.natCast_ne_top _)
    | coe n =>
      have h1' : Fintype.card K ≤ n := Nat.cast_le.1 (WithBot.coe_le_coe.1 h1)
      have hd' : n ≤ d + Fintype.card K := Nat.cast_le.1 (WithBot.coe_le_coe.1 hd)
      refine ⟨n - Fintype.card K, by omega, ?_⟩
      rw [show n - Fintype.card K + Fintype.card K = n by omega]
      rfl

theorem dim_add_one_le_of_lt {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk q r ∈ nonZeroDivisors (R ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrp)

theorem mem_minimalPrimes_of_dim {J₂ q : Ideal (MRing ι)} {d : ℕ} (hq : q.IsPrime) (hrel : IsRelevant q)
    (hJq : J₂ ≤ q)
    (hdim : ∀ W : Ideal (MRing ι), W.IsPrime → J₂ ≤ W → IsRelevant W →
      ringKrullDim (MRing ι ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hqd : ringKrullDim (MRing ι ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    q ∈ J₂.minimalPrimes := by
  obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le hJq
  rcases eq_or_lt_of_le hWq with h | h
  · exact h ▸ hW
  · exfalso
    have := hW.1.1
    have hWrel : IsRelevant W := fun k => by
      obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, fun h' => hi (hWq h')⟩
    have h1 := dim_add_one_le_of_lt h
    have h2 := hdim W hW.1.1 hW.1.2 hWrel
    rw [hqd] at h1
    have h3 := h1.trans h2
    have h' : (((d + Fintype.card K + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        (((d + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast h3
    have : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h'
    omega

theorem abs_geoNum_le [DecidableEq K] (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (x : K → ℤ) :
    |(geoNum n V (fun _ => x) : ℝ)| ≤ coefB n V * nrm x ^ n := by
  rw [geoNum_expand_real n V hS, coefB, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_le_pow (Finset.univ : Finset (Fin n)) (fun i => (x (r i) : ℝ))
    (fun i _ => abs_le_nrm x (r i))
  simpa using this

theorem tdeg_add (a s : K → ℕ) : tdeg (a + s) = tdeg a + tdeg s := by
  simp [tdeg, Finset.sum_add_distrib]

theorem pow_shift_le {a s b : K → ℕ} (h : tdeg b ≤ tdeg a + tdeg s) (m : ℕ) :
    ((tdeg b : ℝ) + 1) ^ m ≤ ((tdeg s : ℝ) + 1) ^ m * ((tdeg a : ℝ) + 1) ^ m := by
  rw [← mul_pow]
  have h' : (tdeg b : ℝ) ≤ tdeg a + tdeg s := by exact_mod_cast h
  have ha : (0 : ℝ) ≤ tdeg a := by positivity
  have hs : (0 : ℝ) ≤ tdeg s := by positivity
  gcongr
  nlinarith

open Classical in

theorem factor_est [DecidableEq K] {J₂ q : Ideal (MRing ι)} {N d : ℕ} (hN : 0 < N) (hq : q.IsPrime)
    (hqm : IsMultiHomogIdeal q) (hNq : (N : MRing ι) ∈ q) (hJq : J₂ ≤ q)
    (hdim : ∀ W : Ideal (MRing ι), W.IsPrime → J₂ ≤ W → IsRelevant W →
      ringKrullDim (MRing ι ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (s c : K → ℕ) :
    ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |lg q (a + s - c) - (if q ∈ topComps J₂ d then appr (Real.log (charOf q)) d q a else 0)| ≤
        C * d * ((tdeg a : ℝ) + 1) ^ (d - 1) := by
  have hcle : ∀ (a : K → ℕ) (a₀ : ℕ), (∀ k, a₀ + tdeg c ≤ a k) → ∀ k, c k ≤ a k ∧ a₀ ≤ (a + s - c) k :=
    fun a a₀ ha k => by
      have h2 : c k ≤ tdeg c :=
        Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      have h3 := ha k
      simp only [Pi.sub_apply, Pi.add_apply]
      omega
  have htb : ∀ a : K → ℕ, tdeg (a + s - c) ≤ tdeg a + tdeg s := fun a =>
    (tdeg_sub_le _ _).trans (tdeg_add a s).le
  by_cases hrel : IsRelevant q
  swap
  · have hnot : q ∉ topComps J₂ d := fun h => hrel h.2.1
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    refine ⟨1 + tdeg c, 0, le_rfl, fun a ha => ?_⟩
    have hpos : 0 < (a + s - c) k := by
      have := (hcle a 1 (fun k' => by have := ha k'; omega) k).2
      omega
    rw [if_neg hnot, lg, card_mPiece_irrel hk hpos]
    simp
  have hv : ¬ IsHorizontal q := not_horizontal_of_mem hN.ne' hNq
  have hp : (charOf q).Prime := charOf_prime hq hv
  have hpq : ((charOf q : ℕ) : MRing ι) ∈ q := natCast_mem_of_charOf q
  have hMP : IsMultiProjPrime q := ⟨hq, hqm, hrel⟩
  have hL : 0 < Real.log (charOf q) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hall := hasymp_all (ι := ι) (L := Real.log (charOf q)) hp geoNum_cut_X geoNum_symm
    (fun W hW hpW hd => hasymp_base hp rfl hW hpW hd)
  by_cases htop : q ∈ topComps J₂ d
  · obtain ⟨⟨a₀', C', hC', hH⟩, hS⟩ := hall d q hMP hpq htop.2.2
    obtain ⟨K1, hK1, hs1⟩ := appr_shift (Real.log (charOf q)) d q hS c
    obtain ⟨K2, hK2, hs2⟩ := appr_shift (Real.log (charOf q)) d q hS s
    refine ⟨a₀' + tdeg c, (C' + K1 + K2) * ((tdeg s : ℝ) + 1) ^ (d - 1), by positivity,
      fun a ha => ?_⟩
    rw [if_pos htop]
    have hx := hcle a a₀' ha
    have h1 := hH (a + s - c) fun k => (hx k).2
    have h2 := hs1 (a + s) fun k => by have := (hx k).1; simp only [Pi.add_apply]; omega
    have h3 := hs2 (a + s) fun k => by simp only [Pi.add_apply]; omega
    rw [add_tsub_cancel_right] at h3
    have m1 := pow_shift_le (htb a) (d - 1)
    have m2 := pow_shift_le (a := a) (s := s) (b := a + s) (tdeg_add a s).le (d - 1)
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have e1 := le_abs_self (lg q (a + s - c) - appr (Real.log (charOf q)) d q (a + s - c))
    have e1' := neg_abs_le (lg q (a + s - c) - appr (Real.log (charOf q)) d q (a + s - c))
    have e2 := le_abs_self (appr (Real.log (charOf q)) d q (a + s) -
      appr (Real.log (charOf q)) d q (a + s - c))
    have e2' := neg_abs_le (appr (Real.log (charOf q)) d q (a + s) -
      appr (Real.log (charOf q)) d q (a + s - c))
    have e3 := le_abs_self (appr (Real.log (charOf q)) d q (a + s) - appr (Real.log (charOf q)) d q a)
    have e3' := neg_abs_le (appr (Real.log (charOf q)) d q (a + s) - appr (Real.log (charOf q)) d q a)
    set P := ((tdeg a : ℝ) + 1) ^ (d - 1)
    set Q := ((tdeg s : ℝ) + 1) ^ (d - 1)
    have hP : 0 ≤ P := by positivity
    have hQ : 0 ≤ Q := by positivity
    have b1 : C' * d * ((tdeg (a + s - c) : ℝ) + 1) ^ (d - 1) ≤ C' * d * (Q * P) := by gcongr
    have b2 : K1 * d * ((tdeg (a + s) : ℝ) + 1) ^ (d - 1) ≤ K1 * d * (Q * P) := by gcongr
    have b3 : K2 * d * ((tdeg (a + s) : ℝ) + 1) ^ (d - 1) ≤ K2 * d * (Q * P) := by gcongr
    rw [abs_le]
    constructor <;> nlinarith
  · obtain ⟨d', hd'd, hqd⟩ := exists_dim_nat hq hqm hrel (hdim q hq hJq hrel)
    have hlt : d' < d := by
      rcases lt_or_eq_of_le hd'd with h | h
      · exact h
      · exfalso
        subst h
        exact htop ⟨mem_minimalPrimes_of_dim hq hrel hJq hdim hqd, hrel, hqd⟩
    obtain ⟨⟨a₀', C', hC', hH⟩, hS⟩ := hall d' q hMP hpq hqd
    have hB := coefB_nonneg d' q
    refine ⟨a₀' + tdeg c, (C' * d' + Real.log (charOf q) * coefB d' q) * ((tdeg s : ℝ) + 1) ^ (d - 1),
      by positivity, fun a ha => ?_⟩
    rw [if_neg htop, sub_zero]
    have hx := hcle a a₀' ha
    set b := a + s - c with hbdef
    have h1 := hH b fun k => (hx k).2
    have hg := abs_geoNum_le d' q hS (fun k => (b k : ℤ))
    rw [nrm_natCast] at hg
    have hf : (1 : ℝ) ≤ d'.factorial := by exact_mod_cast d'.factorial_pos
    have hT : (0 : ℝ) ≤ tdeg b := by positivity
    have hT1 : (1 : ℝ) ≤ (tdeg b : ℝ) + 1 := by linarith
    have happr : |appr (Real.log (charOf q)) d' q b| ≤
        Real.log (charOf q) * coefB d' q * ((tdeg b : ℝ) + 1) ^ (d - 1) := by
      rw [appr, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by linarith : (0 : ℝ) < d'.factorial)]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < d'.factorial)]
      have p1 : (tdeg b : ℝ) ^ d' ≤ ((tdeg b : ℝ) + 1) ^ (d - 1) :=
        (pow_le_pow_left₀ hT (by linarith) d').trans (pow_le_pow_right₀ hT1 (by omega))
      have p2 : |(geoNum d' q (fun _ k => (b k : ℤ)) : ℝ)| ≤ coefB d' q * ((tdeg b : ℝ) + 1) ^ (d - 1) :=
        hg.trans (mul_le_mul_of_nonneg_left p1 hB)
      have p3 : 0 ≤ coefB d' q * ((tdeg b : ℝ) + 1) ^ (d - 1) := by positivity
      calc Real.log (charOf q) * |(geoNum d' q (fun _ k => (b k : ℤ)) : ℝ)|
          ≤ Real.log (charOf q) * (coefB d' q * ((tdeg b : ℝ) + 1) ^ (d - 1)) := by gcongr
        _ ≤ Real.log (charOf q) * coefB d' q * ((tdeg b : ℝ) + 1) ^ (d - 1) * d'.factorial := by
          nlinarith [mul_nonneg hL.le p3]
    have hpow : ((tdeg b : ℝ) + 1) ^ (d' - 1) ≤ ((tdeg b : ℝ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ hT1 (by omega)
    have m1 := pow_shift_le (htb a) (d - 1)
    set P := ((tdeg a : ℝ) + 1) ^ (d - 1)
    set Q := ((tdeg s : ℝ) + 1) ^ (d - 1)
    have hP : 0 ≤ P := by positivity
    have hQ : 0 ≤ Q := by positivity
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hlg : |lg q b| ≤ (C' * d' + Real.log (charOf q) * coefB d' q) * ((tdeg b : ℝ) + 1) ^ (d - 1) := by
      have e := abs_sub_abs_le_abs_sub (lg q b) (appr (Real.log (charOf q)) d' q b)
      have hC'd : 0 ≤ C' * d' := by positivity
      have : C' * d' * ((tdeg b : ℝ) + 1) ^ (d' - 1) ≤ C' * d' * ((tdeg b : ℝ) + 1) ^ (d - 1) := by
        gcongr
      nlinarith
    have hM : 0 ≤ C' * d' + Real.log (charOf q) * coefB d' q := by positivity
    calc |lg q b| ≤ (C' * d' + Real.log (charOf q) * coefB d' q) * ((tdeg b : ℝ) + 1) ^ (d - 1) := hlg
      _ ≤ (C' * d' + Real.log (charOf q) * coefB d' q) * (Q * P) := by gcongr
      _ = (C' * d' + Real.log (charOf q) * coefB d' q) * Q * 1 * P := by ring
      _ ≤ (C' * d' + Real.log (charOf q) * coefB d' q) * Q * d * P := by
        gcongr

theorem ModulePieceHilbert.proof : ModulePieceHilbert.Statement := by
  intro K _ ι _ J₁ J₂ N d hJ₁ hJ₂ hle hN hNJ hdim s
  classical
  obtain ⟨n, F, f, c, q, h0, hlast, hj⟩ := exists_relFiltration J₁ hJ₁ J₂ hJ₂ hle
  have hq : ∀ j, J₂ ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).2.2.1, (hj j).2.2.2.2.2⟩
  have hNq : ∀ j, (N : MRing ι) ∈ q j := fun j => by
    rw [(hj j).2.2.2.2.2]
    have h1 : (N : MRing ι) * f j ∈ J₂ := hNJ _ (hj j).2.1
    rw [← h0] at h1
    exact le_chain (fun j => (hj j).2.2.1) j.castSucc h1
  choose a0 C hC hb using fun j =>
    factor_est hN (hj j).2.2.2.1 (hj j).2.2.2.2.1 (hNq j) (hq j) hdim s (c j)
  refine ⟨∑ j, a0 j + ∑ j, tdeg (c j), (∑ j, C j) * d, fun a ha => ?_⟩
  have ha0 : ∀ j k, a0 j ≤ a k := fun j k => by
    have h1 : a0 j ≤ ∑ j, a0 j := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have := ha k
    omega
  have hca : ∀ j k, c j k ≤ (a + s) k := fun j k => by
    have h1 : c j k ≤ tdeg (c j) :=
      Finset.single_le_sum (f := c j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 : tdeg (c j) ≤ ∑ j, tdeg (c j) :=
      Finset.single_le_sum (f := fun j => tdeg (c j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have := ha k
    simp only [Pi.add_apply]
    omega

  have hcard := modPieceCard_chain (a + s) J₁ n F f c q (h0 ▸ hJ₂) hlast
    (fun j => ⟨(hj j).1, (hj j).2.2.1, (hj j).2.2.2.2.2⟩) hca
  rw [h0] at hcard
  have hlog : Real.log (modPieceCard J₁ J₂ (a + s)) = ∑ j, lg (q j) (a + s - c j) := by
    rw [hcard, Nat.cast_prod, Real.log_prod]
    · rfl
    · intro j _
      exact_mod_cast (card_mPiece_pos _ _ hN (hNq j)).ne'

  have hfin : (topComps J₂ d).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J₂).subset fun W h => h.1
  have hcount : ∀ W ∈ hfin.toFinset,
      ((multAt J₂ W : ℝ) - multAt J₁ W) = ∑ j, if q j = W then (1 : ℝ) else 0 := by
    intro W hW
    have h := multAt_sub_eq_count hJ₁ hle h0 hlast
      (fun j => ⟨(hj j).2.2.1, (hj j).2.2.2.1, (hj j).2.2.2.2.2⟩)
      ((Set.Finite.mem_toFinset hfin).mp hW).1
    have h' := congrArg (Int.cast : ℤ → ℝ) h
    push_cast at h'
    exact h'
  have hsum : (∑ᶠ W ∈ topComps J₂ d, ((multAt J₂ W : ℝ) - multAt J₁ W) * Real.log (charOf W) *
        (geoNum d W (fun _ k => (a k : ℤ)) : ℝ)) / (d.factorial : ℝ) =
      ∑ j, (if q j ∈ topComps J₂ d then appr (Real.log (charOf (q j))) d (q j) a else 0) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_congr rfl fun W hW => by rw [hcount W hW]]
    simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Set.Finite.mem_toFinset, appr]
    split_ifs <;> simp
  rw [hlog, hsum, ← Finset.sum_sub_distrib]
  have hX : (0 : ℝ) < (tdeg a : ℝ) + 1 := by positivity
  have hfinal : (∑ j, C j) * d * ((tdeg a : ℝ) + 1) ^ (d - 1) ≤
      (∑ j, C j) * d * ((tdeg a : ℝ) + 1) ^ d / ((tdeg a : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp
    · rw [mul_div_assoc, show ((tdeg a : ℝ) + 1) ^ d / ((tdeg a : ℝ) + 1) = ((tdeg a : ℝ) + 1) ^ (d - 1) by
        rw [div_eq_iff hX.ne', ← pow_succ, Nat.sub_add_cancel hd0]]
  change _ ≤ (∑ j, C j) * d * ((tdeg a : ℝ) + 1) ^ d / ((tdeg a : ℝ) + 1)
  refine ((Finset.abs_sum_le_sum_abs _ _).trans ?_).trans hfinal
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => hb j a (fun k => ha0 j k)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
