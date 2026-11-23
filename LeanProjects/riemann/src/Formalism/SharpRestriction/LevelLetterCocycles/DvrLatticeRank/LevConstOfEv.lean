import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries

section PS

variable {LL : Type*} [Field LL]

theorem eq_X_mul_shift (f : PowerSeries LL) (h0 : constantCoeff f = 0) :
    f = X * mk (fun k => coeff (k + 1) f) := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

end PS

section Ev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)

def Vs : PowerSeries LL := mk fun k => coeff (k + 1) (W.lev c ζ Eπ)

def Ui : PowerSeries LL := (Vs W c ζ Eπ)⁻¹ ^ h'

def ev (a : LetA O n) (i : ℤ) : LL :=
  if 0 ≤ i + h' then coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') else 0

variable {W c ζ Eπ h'}

theorem levE_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) : W.lev c ζ Eπ = X * Vs W c ζ Eπ :=
  eq_X_mul_shift _ h0

theorem Vs_cc (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : constantCoeff (Vs W c ζ Eπ) ≠ 0 := by
  rw [Vs, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  exact h1

theorem Vs_Ui (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : Vs W c ζ Eπ ^ h' * Ui W c ζ Eπ h' = 1 := by
  rw [Ui, ← mul_pow, PowerSeries.mul_inv_cancel _ (Vs_cc h1), one_pow]

theorem levΛ_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) :
    W.lev c ζ (Eπ ^ h') = X ^ h' * Vs W c ζ Eπ ^ h' := by
  rw [map_pow, levE_eq h0, mul_pow]

theorem levΛ_Ui (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) :
    W.lev c ζ (Eπ ^ h') * Ui W c ζ Eπ h' = X ^ h' := by
  rw [levΛ_eq h0, mul_assoc, Vs_Ui h1, mul_one]

theorem ev_of_lt (a : LetA O n) {i : ℤ} (hi : i + h' < 0) : ev W c ζ Eπ h' a i = 0 := by
  unfold ev
  rw [if_neg (by omega)]

theorem ev_eq (a : LetA O n) {i : ℤ} (hi : 0 ≤ i + h') :
    ev W c ζ Eπ h' a i = coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') := by
  unfold ev
  rw [if_pos hi]

theorem ev_add (a b : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (a + b) i = ev W c ζ Eπ h' a i + ev W c ζ Eπ h' b i := by
  unfold ev
  split_ifs
  · rw [map_add (W.lev c ζ) a b, add_mul, map_add]
  · rw [add_zero]

theorem ev_zero (i : ℤ) : ev W c ζ Eπ h' (0 : LetA O n) i = 0 := by
  unfold ev
  split_ifs <;> simp

theorem ev_sum {ι : Type*} (s : Finset ι) (a : ι → LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (∑ k ∈ s, a k) i = ∑ k ∈ s, ev W c ζ Eπ h' (a k) i := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, ev_zero]) ?_
  intro x s hx ih
  rw [Finset.sum_insert hx, Finset.sum_insert hx, ev_add, ih]

theorem ev_alg (x : O) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (algebraMap O (LetA O n) x * a) i = algebraMap O LL x * ev W c ζ Eπ h' a i := by
  unfold ev
  split_ifs
  · rw [map_mul (W.lev c ζ), AlgHom.commutes, mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul,
      Algebra.smul_def]
  · rw [mul_zero]

theorem ev_letE (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((letE c : LetA O n) * a) i = ev W c ζ Eπ h' a i := by
  unfold ev
  rw [map_mul (W.lev c ζ), Formalism.MainNotions.N.Ln34.ModelFPf.lev_letE (W := W) c ζ, one_mul]

private theorem coeff_lev_pow_eq_zero_of_lt (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (j : ℕ) (hj : j < h') :
    coeff j (W.lev c ζ (Eπ ^ h')) = 0 := by
  rw [levΛ_eq h0, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_lev_eq_sum_coeff_lev_pow_mul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (i : ℕ) :
    coeff i (W.lev c ζ a) = ∑ j ∈ Finset.range (i + h' + 1),
      coeff j (W.lev c ζ (Eπ ^ h')) * ev W c ζ Eπ h' a ((i : ℤ) - j) := by
  have e1 : coeff i (W.lev c ζ a) =
      coeff (i + h') (W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h')) := by
    have e : W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h') = W.lev c ζ a * X ^ h' := by
      rw [← levΛ_Ui h0 h1]
      ring
    rw [e, PowerSeries.coeff_mul_X_pow]
  rw [e1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [ev_eq a (by omega), show ((i : ℤ) - j + h').toNat = i + h' - j by omega]

theorem serMul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module LL V] (a : LetA O n) (d : V) (i : ℤ) :
    serMul (W.lev c ζ (Eπ ^ h')) (fun k => ev W c ζ Eπ h' a k • d) i = serC (W.lev c ζ a) d i := by
  unfold serMul serC
  split_ifs with hi
  · obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (i' + h' + 1)) ?_]
    · simp only [smul_smul, ← Finset.sum_smul]
      rw [Int.toNat_natCast, coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i']
    · intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hj
      simp only
      rw [ev_of_lt a (by omega), zero_smul, smul_zero]
  · have hz : (fun j : ℕ => coeff j (W.lev c ζ (Eπ ^ h')) •
        (fun k => ev W c ζ Eπ h' a k • d) (i - j)) = fun _ => 0 := by
      funext j
      by_cases hj : j < h'
      · rw [coeff_lev_pow_eq_zero_of_lt h0 j hj, zero_smul]
      · simp only
        rw [ev_of_lt a (by omega), zero_smul, smul_zero]
    rw [hz, finsum_zero]

theorem lev_zero_of_ev (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) (a : LetA O n) (t₀ : ℤ)
    (h : ∀ t < t₀, ev W c ζ Eπ h' a t = 0) (i : ℕ) (hi : (i : ℤ) < t₀ + h') :
    coeff i (W.lev c ζ a) = 0 := by
  have e : W.lev c ζ a = (W.lev c ζ a * Ui W c ζ Eπ h') * Vs W c ζ Eπ ^ h' := by
    rw [mul_assoc, mul_comm (Ui W c ζ Eπ h'), Vs_Ui h1, mul_one]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hev := h ((p.1 : ℤ) - h') (by omega)
  rw [ev_eq a (by omega), show ((p.1 : ℤ) - h' + h').toNat = p.1 by omega] at hev
  rw [hev, zero_mul]

theorem lev_const_of_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (t₁ : ℤ) (h : ∀ t < t₁, t ≠ 0 → ev W c ζ Eπ h' a t = 0) (i : ℕ)
    (hi : (i : ℤ) < t₁ + h') :
    coeff i (W.lev c ζ a) = ev W c ζ Eπ h' a 0 * coeff i (W.lev c ζ (Eπ ^ h')) := by
  rw [coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i, Finset.sum_eq_single i]
  · rw [sub_self, mul_comm]
  · intro j _ hji
    by_cases hjh : j < h'
    · rw [coeff_lev_pow_eq_zero_of_lt h0 j hjh, zero_mul]
    · rw [h ((i : ℤ) - j) (by omega) (by omega), mul_zero]
  · intro hi'
    exact absurd (Finset.mem_range.mpr (by omega)) hi'

end Ev

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
