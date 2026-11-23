import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency

noncomputable section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

namespace CompactOperatorsAlt

section Below

variable {K : Type} [Field K] {R : Subring K}

theorem below_mul {n : ℕ} {f h : PowerSeries K} (hf : ∀ m < n, coeff m f ∈ R)
    (hh : ∀ m < n, coeff m h ∈ R) : ∀ m < n, coeff m (f * h) ∈ R := by
  intro m hm
  rw [PowerSeries.coeff_mul]
  refine Subring.sum_mem _ fun p hp => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact R.mul_mem (hf _ (by omega)) (hh _ (by omega))

theorem below_subst {n : ℕ} {A a : PowerSeries K} (hA : IntPS R A)
    (ha0 : constantCoeff a = 0) (ha : ∀ m < n, coeff m a ∈ R) :
    ∀ m < n, coeff m (A.subst a) ∈ R := by
  intro m hm
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' ha0)]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun k => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hA k) (Pts.coeff_pow_mem ha k m hm)

theorem below_shift {n : ℕ} {g : PowerSeries K} {al : K} (hal : al ∈ R)
    (hg : ∀ m < n, coeff m g ∈ R) : ∀ m < n + 1, coeff m (C al * X * g) ∈ R := by
  intro m hm
  have h : C al * X * g = X * (C al * g) := by ring
  rw [h]
  cases m with
  | zero => rw [coeff_zero_X_mul]; exact R.zero_mem
  | succ m => rw [coeff_succ_X_mul, coeff_C_mul]; exact R.mul_mem hal (hg m (by omega))

theorem coeff_of_sq {n : ℕ} {g : PowerSeries K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : constantCoeff g = 1) (hg : ∀ m < n, coeff m g ∈ R) (hgg : coeff n (g * g) ∈ R) :
    coeff n g ∈ R := by
  have h1 : IntPS R (1 : PowerSeries K) := by simpa using USideA.intPS_X_pow (R := R) (K := K) 0
  have hh0 : coeff 0 (g - 1) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]
  have hh : ∀ m < n, coeff m (g - 1) ∈ R := fun m hm => by
    rw [map_sub]; exact R.sub_mem (hg m hm) (h1 m)
  have hid : coeff n (g - 1) = (2 : K)⁻¹ * (coeff n (g * g) - coeff n (1 : PowerSeries K)
      - coeff n ((g - 1) * (g - 1))) := by
    have : g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1) := by ring
    rw [← map_sub, ← map_sub, this, map_add]
    field_simp
    ring
  have hk : coeff n (g - 1) ∈ R := by
    rw [hid, PowerSeries.coeff_mul n (g - 1)]
    refine R.mul_mem h2 (R.sub_mem (R.sub_mem hgg (h1 n)) (Subring.sum_mem _ fun p hp => ?_))
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases hp1 : p.1 = 0
    · rw [hp1, hh0, zero_mul]; exact R.zero_mem
    by_cases hp2 : p.2 = 0
    · rw [hp2, hh0, mul_zero]; exact R.zero_mem
    exact R.mul_mem (hh _ (by omega)) (hh _ (by omega))
  have : g = (g - 1) + 1 := by ring
  rw [this, map_add]
  exact R.add_mem hk (h1 n)

theorem int_of_eq {A V g : PowerSeries K} {al : K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hA : IntPS R A) (hV : IsOneUnit R V) (hal : al ∈ R) (hg0 : constantCoeff g = 1)
    (hEq : A.subst (C al * X * g) = g * g * V) : IntPS R g := by
  have hne : constantCoeff V ≠ 0 := by rw [hV.1]; exact one_ne_zero
  have hinv : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hne
  have hW : IntPS R V⁻¹ := USideA.intPS_of_mul_eq_one hV.2 hV.1 hinv
  have hgg : g * g = A.subst (C al * X * g) * V⁻¹ := by
    rw [hEq, mul_assoc, hinv, mul_one]
  have ha0 : constantCoeff (C al * X * g) = 0 := by simp
  have key : ∀ n, ∀ m < n, coeff m g ∈ R := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · exact ih m h
      · subst h
        refine coeff_of_sq h2 h20 hg0 ih ?_
        rw [hgg]
        exact below_mul (below_subst hA ha0 (below_shift hal ih)) (fun k _ => hW k) m
          (Nat.lt_succ_self m)
  exact fun n => key (n + 1) n (Nat.lt_succ_self n)

theorem isOneUnit_veluXs {A : PowerSeries K} {ι : Type} [Fintype ι] {xs : ι → PowerSeries K}
    {xP : ι → K} {r : K} (hA : IsOneUnit R A) (hxs : ∀ P, IntPS R (xs P)) (hxP : ∀ P, xP P ∈ R)
    (hr : r ∈ R) : IsOneUnit R (veluXs A xs xP r) := by
  refine ⟨by simp [veluXs, hA.1], ?_⟩
  exact USideA.intPS_add hA.2 (USideA.intPS_mul (USideA.intPS_X_pow 2)
    (USideA.intPS_sub (USideA.intPS_sum _ fun P _ =>
      USideA.intPS_sub (hxs P) (USideA.intPS_C (hxP P))) (USideA.intPS_C hr)))

theorem exists_mulBy_eq {l linv : PowerSeries K} (h : IsLogPair l linv) {al : K} (hal : al ≠ 0) :
    ∃ g : PowerSeries K, constantCoeff g = 1 ∧ mulBy l linv al = C al * X * g := by
  have ha0 : constantCoeff (C al * l) = 0 := by rw [map_mul, h.1, mul_zero]
  have hv0 : coeff 0 (mulBy l linv al) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact Pts.constantCoeff_mulBy h al
  have hv1 : coeff 1 (mulBy l linv al) = al := by
    have hc := IntegralMvPolynomialLemmas.coeff_subst_congr (g := linv) (h := (X : PowerSeries K)) (a := C al * l) ha0
      (Finsupp.single () 1) (fun k hk => by
        rw [Finsupp.degree_single] at hk
        interval_cases k
        · simp [h.2.2.1]
        · rw [Pts.coeff_one_linv h, coeff_one_X])
    rw [PowerSeries.subst_X (Pts.hasSubst ha0)] at hc
    have h1 : coeff 1 (mulBy l linv al) = coeff 1 (C al * l) := hc
    rw [h1, coeff_C_mul, h.2.1, mul_one]
  refine ⟨PowerSeries.mk fun n => al⁻¹ * coeff (n + 1) (mulBy l linv al), ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, hv1, inv_mul_cancel₀ hal]
  · have hr : ∀ g : PowerSeries K, C al * X * g = X * (C al * g) := fun g => by ring
    rw [hr]
    ext n
    cases n with
    | zero => rw [coeff_zero_X_mul, hv0]
    | succ n => rw [coeff_succ_X_mul, coeff_C_mul, coeff_mk, mul_inv_cancel_left₀ hal]

end Below

theorem ne_zero_of_isEndoR {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {al albar : K}
    (hN : al * albar = (Fintype.card ι : K) + 1) : al ≠ 0 := by
  intro h
  rw [h, zero_mul] at hN
  exact (Nat.cast_add_one_ne_zero (R := K) (Fintype.card ι)) hN.symm

end CompactOperatorsAlt

open CompactOperatorsAlt

theorem velu_x_coordinate_integral : VeluIntegralX := by
  intro K _ _ R A g ι _ xs xP al r hA hxs hxP hr hal hal0 h2 hg0 hEq
  refine int_of_eq h2 two_ne_zero hA.2 (isOneUnit_veluXs hA hxs hxP hr) hal hg0 ?_
  have hC : (C (al ^ 2) : PowerSeries K) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [constantCoeff_C, map_zero] at this
    exact pow_ne_zero 2 hal0 this
  have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h0 : C (al ^ 2) * X ^ 2 *
      (A.subst (C al * X * g) - g * g * veluXs A xs xP r) = 0 := by
    have : C (al ^ 2) * X ^ 2 * (A.subst (C al * X * g) - g * g * veluXs A xs xP r) =
        C (al ^ 2) * A.subst (C al * X * g) * X ^ 2 -
          (C al * X * g) ^ 2 * veluXs A xs xP r := by
      rw [map_pow]; ring
    rw [this, hEq, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero hC hX))

theorem integral_endomorphism_from_datum : EndIntFromDatum := by
  intro K _ _ R e l linv A c0 ι _ neg xP w xs al albar hL hX hA h2 hD
  obtain ⟨hZ, hN, hw, hxs, hxP, hal, -, hr⟩ := hD
  have hal0 : al ≠ 0 := ne_zero_of_isEndoR hN
  obtain ⟨g, hg0, hvg⟩ := exists_mulBy_eq hL hal0
  have hV := veluXFromZ K e l linv A c0 ι neg xP w xs al hL hX hZ hw
  rw [hvg] at hV
  have hg : IntPS R g :=
    velu_x_coordinate_integral K R A g ι xs xP al _ hA hxs hxP hr hal hal0 h2 hg0 hV
  show IntPS R (mulBy l linv al)
  rw [hvg]
  exact USideA.intPS_mul (USideA.intPS_mul (USideA.intPS_C hal) USideA.intPS_X) hg

theorem phi_norm_from_datum : PhNormFromDatum := by
  intro K _ _ R e s2 l linv ph A c0 ι _ neg xP w xs al albar hL hPh hX hA h2 hD hs
  have hE : EndInt R l linv al :=
    integral_endomorphism_from_datum K R e l linv A c0 ι neg xP w xs al albar hL hX hA h2 hD
  obtain ⟨hZ, hN, -, -, hxP, hal, hali, -⟩ := hD
  have hal0 : al ≠ 0 := ne_zero_of_isEndoR hN
  have hI : IsogenyFormula e s2 (fun P => xP P + c0) al :=
    (isogenyIffBar K e s2 ι neg xP c0 w al albar hal0 hN hZ).mpr hs
  have := phNormUnit K R e s2 l linv ph A c0 ι xP al hL hPh hX hI hA hxP hal hali hal0 h2 hE
  show Cong R (PowerSeries.subst (mulBy l linv al) ph) ((al * albar) • ph)
  rw [hN]
  exact this

theorem endoAllFromData_of (hA : EndoAll) : EndoAllFromData := by
  intro K _ _ _ _ R hR e s2 l linv ph A c0 hF hF1 hPh hX hA1 O _ _ _ τ hτ hstar hself h2 h2O hsum
    Dn hDn hdata
  refine hA K R hR l linv ph hF hF1 O τ hτ hstar hself h2 h2O hsum Dn hDn ?_
  intro α hα
  obtain ⟨ι, _, neg, xP, w, xs, hD, hs⟩ := hdata α hα
  exact ⟨integral_endomorphism_from_datum K R e l linv A c0 ι neg xP w xs _ _ hF.1 hX hA1 h2 hD,
    phi_norm_from_datum K R e s2 l linv ph A c0 ι neg xP w xs _ _ hF.1 hPh hX hA1 h2 hD hs⟩

end Formalism.L2.Th1.C
