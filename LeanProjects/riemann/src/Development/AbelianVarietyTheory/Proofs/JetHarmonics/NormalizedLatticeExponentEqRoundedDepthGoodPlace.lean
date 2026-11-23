import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : HeightOneSpectrum (𝓞 K))

theorem vwUnit_mul {x y : K} (hx : x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) (hy : y ≠ 0 ∧ Formalism.DivisionValues.vw v y = 0) :
    x * y ≠ 0 ∧ Formalism.DivisionValues.vw v (x * y) = 0 :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul v _ _ hx.1 hy.1, hx.2, hy.2, add_zero]⟩

theorem vwUnit_nat {N : ℕ} (hN : ¬ plc v ∣ N) : (N : K) ≠ 0 ∧ Formalism.DivisionValues.vw v (N : K) = 0 := by
  have h0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  refine ⟨by exact_mod_cast h0, ?_⟩
  rw [DepthTie.vw_N v N h0, padicValNat.eq_zero_of_not_dvd hN]
  simp

theorem vwUnit_pow {x : K} (hx : x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) (n : ℕ) :
    x ^ n ≠ 0 ∧ Formalism.DivisionValues.vw v (x ^ n) = 0 := by
  induction n with
  | zero =>
    have := vwUnit_nat v (N := 1) (by simpa using (plc_prime v).ne_one)
    simpa using this
  | succ n ih => rw [pow_succ]; exact vwUnit_mul v ih hx

theorem vwUnit_prime {p : ℕ} (hp : p.Prime) (h : plc v ≠ p) : (p : K) ≠ 0 ∧ Formalism.DivisionValues.vw v (p : K) = 0 :=
  vwUnit_nat v fun hd => h ((Nat.prime_dvd_prime_iff_eq (plc_prime v) hp).1 hd)

theorem vwUnit_factor {x y : K} (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (h : x * y ≠ 0 ∧ Formalism.DivisionValues.vw v (x * y) = 0) :
    (x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) ∧ (y ≠ 0 ∧ Formalism.DivisionValues.vw v y = 0) := by
  have x0 := left_ne_zero_of_mul h.1
  have y0 := right_ne_zero_of_mul h.1
  have h2 := h.2
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul v _ _ x0 y0] at h2
  have a := DepthTie.vw_nonneg_of_isIntegral v x hx
  have b := DepthTie.vw_nonneg_of_isIntegral v y hy
  exact ⟨⟨x0, by omega⟩, ⟨y0, by omega⟩⟩

end Units

theorem vw_sigAt_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dd : DepData E) {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 E) K]
    (hsp : PiSplit (H := H) Dd) (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (h2 : plc v ∉ Dd.Q.sm) (hq : plc v ≠ Dd.Q.q1) (hd : plc v ≠ Dd.Q.dd)
    (hg1 : plc v ≠ Dd.Q.g1) (hg2 : plc v ≠ Dd.Q.g2) (Dw' : Datum H) (j : ℕ) :
    Formalism.DivisionValues.vw v (sigAt (Dw := Dw') (H := H) (LL := K) Dd j) = 0 := by
  obtain ⟨e0, e1, -⟩ := DepthTie.alg_pi_ne_zero (K := K) Dd hsp ⟨hprime.1, hprime.2.1⟩
  have u1 := vwUnit_prime v hprime.1 hg1
  have u2 := vwUnit_prime v hprime.2.1 hg2
  have uq := vwUnit_prime v hprime.2.2.1 hq
  have ud := vwUnit_prime v hprime.2.2.2 hd
  have ut : ∀ a : ℕ → ℕ, ((∏ p ∈ Dd.Q.sm.filter Nat.Prime, p ^ a p : ℕ) : K) ≠ 0 ∧
      Formalism.DivisionValues.vw v ((∏ p ∈ Dd.Q.sm.filter Nat.Prime, p ^ a p : ℕ) : K) = 0 := fun a => vwUnit_nat v fun hdv => by
    obtain ⟨p, hp, h⟩ := (Prime.dvd_finset_prod_iff (plc_prime v).prime _).1 hdv
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    exact h2 ((Nat.prime_dvd_prime_iff_eq (plc_prime v) hp2).1 ((plc_prime v).dvd_of_dvd_pow h) ▸ hp1)
  obtain ⟨a0, b0⟩ := vwUnit_factor v (DepthTie.isIntegral_alg _) (DepthTie.isIntegral_alg _) (e0 ▸ u1)
  obtain ⟨a1, b1⟩ := vwUnit_factor v (DepthTie.isIntegral_alg _) (DepthTie.isIntegral_alg _) (e1 ▸ u2)
  rw [DepthTie.sigAt_eq]
  refine (vwUnit_mul v ?_ ?_).2
  · unfold nnKAt nnOf
    rw [Fin.prod_univ_two]
    exact vwUnit_mul v (vwUnit_mul v (vwUnit_pow v b0 _) (vwUnit_pow v a0 _))
      (vwUnit_mul v (vwUnit_pow v b1 _) (vwUnit_pow v a1 _))
  · unfold DepthTie.Nsig DepPage.Z1 DepPage.q
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact vwUnit_mul v (vwUnit_pow v (vwUnit_mul v u1 u2) _)
      (vwUnit_mul v (vwUnit_mul v (ut _) (vwUnit_pow v uq _)) (vwUnit_pow v ud _))

theorem normalizedLattice_exponent_eq_roundedDepth_goodPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  intro E _ _ _ H lv Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι hE hσ hpr hsp hPg v j hv
  obtain ⟨hprime, -, -⟩ := DepthTie.page_facts Dd O hPg hpr
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpr
  rw [p1, p2, p3, p4, p5] at hv
  simp only [not_or] at hv
  obtain ⟨h2, hq, hd, hg1, hg2⟩ := hv
  have hs := vw_sigAt_good Dd hsp hprime v h2 hq hd hg1 hg2 (Dw (ι j)) (ι j)
  obtain ⟨o1, o2⟩ := DepthTie.one_le_ramOver_below (F := c.F) v
  have hW : 0 ≤ (nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal :=
    EReal.toReal_nonneg (le_max_left _ _)
  have hram : ¬ Dd.Q.IsRam (plc v) := by
    unfold DepPage.IsRam; tauto
  have hbad : ¬ Dd.Q.IsBad (plc v) := by
    unfold DepPage.IsBad; tauto
  have r1 : (1 : ℝ) ≤ (ramOver (K := c.F) v : ℝ) := by exact_mod_cast o1
  have r2 : (1 : ℝ) ≤ (ramOverZ (placeBelow (K := c.F) v) : ℝ) := by exact_mod_cast o2
  have key : O.e0 v j = (⌈(ramOverZ (placeBelow (K := c.F) v) : ℝ) * (Dd.Q.T : ℝ) *
      ((nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal /
        (ramOverZ (placeBelow (K := c.F) v) : ℝ))⌉ : ℝ) / (ramOverZ (placeBelow (K := c.F) v) : ℝ) := by
    unfold OnObj.e0
    rw [hE v j, hσ v j, hs, DepthTie.ramw_eq_below (F := c.F) v]
    unfold EAt expE DepPage.eLam nuStarAt DepPage.nuN DepPage.cP
    simp only []
    rw [DepthTie.resChar_below (F := c.F) v, if_neg hg1, if_neg hg2, if_neg hram, if_neg hbad]
    simp only [Nat.cast_zero, add_zero, Int.cast_zero, sub_zero, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    rw [mul_div_mul_left _ _ (by linarith)]
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.ceil_nonneg (by positivity))]
  refine ⟨?_, fun h0 => ?_⟩
  · rw [key, div_le_iff₀ (by linarith)]
    refine (Int.ceil_lt_add_one _).le.trans ?_
    nlinarith
  · rw [key, h0]
    simp

end GlobalTheory.GoodDepth
