import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerateOfUnitSeriesIntegral
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C]

def ex {σ : Type} (f : MvPowerSeries σ C) : MvPowerSeries σ C := PowerSeries.subst f (PowerSeries.exp C)

theorem expS_eq {n dd : ℕ} (f : PS C n dd) : FB.expS C f = ex f := rfl

theorem exp_biv : ex (X 0 + X 1 : MvPowerSeries (Fin 2) C) = ex (X 0) * ex (X 1) := by
  ext e
  unfold ex
  rw [PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp]
  rw [← map_natCast (algebraMap ℚ C), ← map_mul, ← map_mul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial (e 0) (e 1)
  have h' : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    rw [Nat.choose_symm_add]; exact_mod_cast h
  have h0 : ((e 0).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h1 : ((e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h2 : ((e 0 + e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  linarith

theorem subst_ex {σ τ : Type} [Finite σ] (h : σ → MvPowerSeries τ C)
    (hh : ∀ i, constantCoeff (h i) = 0) (f : MvPowerSeries σ C) (hf : constantCoeff f = 0) :
    subst h (ex f) = ex (subst h f) := by
  have hs : HasSubst h := hasSubst_of_constantCoeff_zero hh
  have ha : HasSubst (fun _ : Unit => f) :=
    PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hf)
  unfold ex
  rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply ha hs]

theorem ex_add {σ : Type} (f g : MvPowerSeries σ C) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : ex (f + g) = ex f * ex g := by
  have hh : ∀ i, constantCoeff ((![f, g] : Fin 2 → MvPowerSeries σ C) i) = 0 := by
    intro i; fin_cases i <;> simp [hf, hg]
  have hs : HasSubst (![f, g] : Fin 2 → MvPowerSeries σ C) := hasSubst_of_constantCoeff_zero hh
  have key := congrArg (subst (![f, g] : Fin 2 → MvPowerSeries σ C)) (exp_biv (C := C))
  rw [subst_mul hs, subst_ex _ hh _ (by simp), subst_ex _ hh _ (by simp),
    subst_ex _ hh _ (by simp), subst_add hs, subst_X hs, subst_X hs] at key
  simpa using key

theorem ex_zero {σ : Type} : ex (0 : MvPowerSeries σ C) = 1 := by
  apply MvPowerSeries.ext; intro n
  rw [ex, PowerSeries.coeff_subst PowerSeries.HasSubst.zero, finsum_eq_single _ 0]
  · simp
  · intro d hd; simp [zero_pow hd]

theorem ex_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C) (hf : ∀ i, constantCoeff (f i) = 0) :
    ex (∑ i ∈ s, f i) = ∏ i ∈ s, ex (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Finset.prod_empty]
    exact ex_zero
  · intro i s hi ih
    have h0 : constantCoeff (∑ j ∈ s, f j) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => hf j
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ex_add _ _ (hf i) h0, ih]

theorem ev_ex {m n dd : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (f : PS C m dd) (hf : constantCoeff f = 0) :
    ev a (ex f) = ex (ev a f) := by
  unfold ev
  exact subst_ex (fun p : Fin m × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f hf

theorem intS_of_mul_eq_one {σ : Type} {V : VF C} {u v : MvPowerSeries σ C} (huv : u * v = 1)
    (hu0 : constantCoeff u = 1) (hu : IntS V u) : IntS V v := by
  have main : ∀ (m : ℕ) (d : σ →₀ ℕ), d.degree = m → V.Ge 0 (coeff d v) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hd
      have h1 := congrArg (coeff d) huv
      rw [coeff_mul,
        ← Finset.add_sum_erase _ _ (show ((0 : σ →₀ ℕ), d) ∈ Finset.HasAntidiagonal.antidiagonal d by simp)] at h1
      simp only [coeff_zero_eq_constantCoeff_apply, hu0, one_mul] at h1
      have h2 : coeff d v = coeff d (1 : MvPowerSeries σ C) +
          - ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal d).erase ((0 : σ →₀ ℕ), d), coeff p.1 u * coeff p.2 v := by
        rw [← h1]; ring
      rw [h2]
      refine VF.Ge.add (intS_one d) (VF.Ge.neg (VF.Ge.sum fun p hp => ?_))
      have hp1 : p.1 + p.2 = d := by simpa using (Finset.mem_erase.mp hp).2
      have hp2 : p ≠ (0, d) := (Finset.mem_erase.mp hp).1
      have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp1]
      have hne : p.1 ≠ 0 := by
        intro h0
        apply hp2
        ext1
        · exact h0
        · simpa [h0] using hp1
      have hpos : p.1.degree ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff _).mp h)
      exact (hu _).mul_int (ih p.2.degree (by omega) p.2 rfl)
  exact fun d => main _ d rfl

variable {dd : ℕ}

theorem multiplication_constantCoeff_zero (G : FGLaw C dd) (n : ℕ) (i : Fin dd) : constantCoeff (mulL G.F n i) = 0 := by
  induction n generalizing i with
  | zero => show constantCoeff (0 : PS C 1 dd) = 0; exact map_zero _
  | succ n ih =>
    show constantCoeff (ev ![mulL G.F n, pt C dd 0] (G.F i)) = 0
    refine const_ev (fun k j => ?_) (G.const i)
    fin_cases k
    · exact ih j
    · exact z0_pt 0 j

theorem mulL_int {V : VF C} (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (n : ℕ) (i : Fin dd) :
    IntS V (mulL G.F n i) := by
  induction n generalizing i with
  | zero => show IntS V (0 : PS C 1 dd); exact fun μ => by rw [map_zero]; exact VF.Ge.zero 0
  | succ n ih =>
    show IntS V (ev ![mulL G.F n, pt C dd 0] (G.F i))
    refine intS_ev (fun k j => ?_) (fun k j => ?_) (hF i)
    · fin_cases k
      · exact multiplication_constantCoeff_zero G n j
      · exact z0_pt 0 j
    · fin_cases k
      · exact ih j
      · exact intS_X _

theorem mulL_one (G : FGLaw C dd) : mulL G.F 1 = pt C dd 0 := by
  funext i
  exact G.unit i

def mm2 (G : FGLaw C dd) (n : ℕ) : Pt C 2 dd := comp1 (mulL G.F n) (pt C (n := 2) dd 0)

theorem double_multiplication_constantCoeff (G : FGLaw C dd) (n : ℕ) (i : Fin dd) : constantCoeff (mm2 G n i) = 0 :=
  const_ev (fun k j => by fin_cases k; exact z0_pt 0 j) (multiplication_constantCoeff_zero G n i)

theorem double_multiplication_integral {V : VF C} (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (n : ℕ) (i : Fin dd) :
    IntS V (mm2 G n i) :=
  intS_ev (fun k j => by fin_cases k; exact z0_pt 0 j) (fun k j => by fin_cases k; exact intS_X _)
    (mulL_int G hF n i)

theorem double_multiplication_one (G : FGLaw C dd) : mm2 G 1 = pt C (n := 2) dd 0 := by
  funext i
  unfold mm2 comp1
  rw [mulL_one]
  exact ev_X (fun k j => by fin_cases k; exact z0_pt 0 j) 0 i

theorem double_multiplication_succ (G : FGLaw C dd) (n : ℕ) (i : Fin dd) :
    mm2 G (n + 1) i = ev ![mm2 G n, pt C (n := 2) dd 0] (G.F i) := by
  have h1 : Z0 (![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) := fun k j => by fin_cases k; exact z0_pt 0 j
  have h2 : Z0 (![mulL G.F n, pt C dd 0] : Fin 2 → Pt C 1 dd) := fun k j => by
    fin_cases k
    · exact multiplication_constantCoeff_zero G n j
    · exact z0_pt 0 j
  show ev ![pt C (n := 2) dd 0] (ev ![mulL G.F n, pt C dd 0] (G.F i)) = _
  rw [ev_ev h2 h1]
  congr 1
  funext k j
  fin_cases k
  · rfl
  · exact ev_X h1 0 j

variable {V : VF C} {O : Type} [CommRing O] [StarRing O]

def gg (Y : FBChart C V O dd) (n : ℕ) : PS C 2 dd := ev ![mm2 Y.B.G n, pt C (n := 2) dd 1] Y.h

theorem constant_zero_multiplication_triple (Y : FBChart C V O dd) (n : ℕ) :
    Z0 (![mm2 Y.B.G n, pt C (n := 2) dd 0, pt C (n := 2) dd 1] : Fin 3 → Pt C 2 dd) := fun k j => by
  fin_cases k
  · exact double_multiplication_constantCoeff Y.B.G n j
  · exact z0_pt 0 j
  · exact z0_pt 1 j

theorem constant_zero_double_multiplication_pair (Y : FBChart C V O dd) (n : ℕ) :
    Z0 (![mm2 Y.B.G n, pt C (n := 2) dd 1] : Fin 2 → Pt C 2 dd) := fun k j => by
  fin_cases k
  · exact double_multiplication_constantCoeff Y.B.G n j
  · exact z0_pt 1 j

theorem height_multiple_constantCoeff (Y : FBChart C V O dd) (n : ℕ) : constantCoeff (gg Y n) = 0 :=
  const_ev (constant_zero_double_multiplication_pair Y n) (h_const Y)

def p1 (Y : FBChart C V O dd) (n : ℕ) : PS C 2 dd :=
  ev ![mm2 Y.B.G n, pt C (n := 2) dd 0, pt C (n := 2) dd 1] Y.B.ph1

theorem first_partial_unit_eq_exp (Y : FBChart C V O dd) (n : ℕ) : p1 Y n = ex (gg Y n + Y.h - gg Y (n + 1)) := by
  have hph : Y.B.ph1 = ex (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) := by
    have := Y.gauge.ph1
    rwa [toK_self, FK_self] at this
  have h3 := constant_zero_multiplication_triple Y n
  have hA : Z0 (![pt C (n := 3) dd 0, pt C dd 2] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact z0_pt 0 j
    · exact z0_pt 2 j
  have hB : Z0 (![pt C (n := 3) dd 1, pt C dd 2] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact z0_pt 1 j
    · exact z0_pt 2 j
  have hPP : Z0 (![pt C (n := 3) dd 0, pt C dd 1] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact z0_pt 0 j
    · exact z0_pt 1 j
  have hadd : ∀ j, constantCoeff (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) = 0 := fun j =>
    const_ev hPP (Y.B.G.const j)
  have hC : Z0 (![addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact hadd j
    · exact z0_pt 2 j
  have hE0 : constantCoeff (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) = 0 := by
    rw [map_sub, map_add, const_ev hA (h_const Y), const_ev hB (h_const Y), const_ev hC (h_const Y)]
    simp
  unfold p1
  rw [hph, ev_ex h3 _ hE0, ev_sub h3, ev_add h3, ev_ev hA h3, ev_ev hB h3, ev_ev hC h3]
  congr 1
  have eA : (fun k i => ev ![mm2 Y.B.G n, pt C (n := 2) dd 0, pt C (n := 2) dd 1]
      ((![pt C (n := 3) dd 0, pt C dd 2] : Fin 2 → Pt C 3 dd) k i)) = ![mm2 Y.B.G n, pt C (n := 2) dd 1] := by
    funext k i
    fin_cases k
    · exact ev_X h3 0 i
    · exact ev_X h3 2 i
  have eB : (fun k i => ev ![mm2 Y.B.G n, pt C (n := 2) dd 0, pt C (n := 2) dd 1]
      ((![pt C (n := 3) dd 1, pt C dd 2] : Fin 2 → Pt C 3 dd) k i)) = ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] := by
    funext k i
    fin_cases k
    · exact ev_X h3 1 i
    · exact ev_X h3 2 i
  have eC : (fun k i => ev ![mm2 Y.B.G n, pt C (n := 2) dd 0, pt C (n := 2) dd 1]
      ((![addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) k i)) =
      ![mm2 Y.B.G (n + 1), pt C (n := 2) dd 1] := by
    funext k i
    fin_cases k
    · show ev ![mm2 Y.B.G n, pt C (n := 2) dd 0, pt C (n := 2) dd 1]
          (ev ![pt C (n := 3) dd 0, pt C dd 1] (Y.B.G.F i)) = mm2 Y.B.G (n + 1) i
      rw [ev_ev hPP h3, double_multiplication_succ]
      congr 1
      funext k' j
      fin_cases k'
      · exact ev_X h3 0 j
      · exact ev_X h3 1 j
    · exact ev_X h3 2 i
  rw [eA, eB, eC, PartialDerivEval.eval_points_two]
  rfl

theorem sum_height_telescope (Y : FBChart C V O dd) (L : ℕ) (hL : 1 ≤ L) :
    ∑ i ∈ Finset.range (L - 1), (gg Y (i + 1) + Y.h - gg Y (i + 1 + 1)) = Y.h - gg Y L + (L - 1) • Y.h := by
  have e : ∀ i ∈ Finset.range (L - 1), gg Y (i + 1) + Y.h - gg Y (i + 1 + 1) =
      (gg Y (i + 1) - gg Y (i + 1 + 1)) + Y.h := fun i _ => by abel
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun i => gg Y (i + 1)) (L - 1), Finset.sum_const, Finset.card_range]
  have h1 : gg Y 1 = Y.h := by
    unfold gg; rw [double_multiplication_one]; exact PartialDerivEval.eval_points_two _
  have h2 : L - 1 + 1 = L := by omega
  simp only [zero_add, h2, h1]

theorem second_coord_mul_inner (Y : FBChart C V O dd) : Y.u1 * ∏ i ∈ Finset.range (V.l - 1), p1 Y (i + 1) = 1 := by
  have hl : 1 ≤ V.l := V.l_prime.one_lt.le
  have hu : Y.u1 = ex (gg Y V.l - (V.l : C) • Y.h) := rfl
  have hE : ∀ i, constantCoeff (gg Y (i + 1) + Y.h - gg Y (i + 1 + 1)) = 0 := fun i => by
    rw [map_sub, map_add, height_multiple_constantCoeff, height_multiple_constantCoeff, h_const]; simp
  have hprod : ∏ i ∈ Finset.range (V.l - 1), p1 Y (i + 1) =
      ex (∑ i ∈ Finset.range (V.l - 1), (gg Y (i + 1) + Y.h - gg Y (i + 1 + 1))) := by
    rw [ex_sum _ _ hE]
    exact Finset.prod_congr rfl fun i _ => first_partial_unit_eq_exp Y (i + 1)
  have hU0 : constantCoeff (gg Y V.l - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, height_multiple_constantCoeff, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, h_const, mul_zero, sub_zero]
  have hS0 : constantCoeff (∑ i ∈ Finset.range (V.l - 1), (gg Y (i + 1) + Y.h - gg Y (i + 1 + 1))) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hE i
  rw [hu, hprod, ← ex_add _ _ hU0 hS0, sum_height_telescope Y V.l hl]
  have key : ∀ (A B : PS C 2 dd) (L : ℕ), 1 ≤ L → A - L • B + (B - A + (L - 1) • B) = 0 := by
    intro A B L hL
    obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
    rw [Nat.add_sub_cancel, succ_nsmul]
    abel
  have e : gg Y V.l - (V.l : C) • Y.h + (Y.h - gg Y V.l + (V.l - 1) • Y.h) = 0 := by
    rw [Nat.cast_smul_eq_nsmul C]
    exact key _ _ _ hl
  rw [e, ex_zero]

theorem first_partial_unit_integral (Y : FBChart C V O dd) (n : ℕ) : IntS V (p1 Y n) := by
  refine intS_ev (constant_zero_multiplication_triple Y n) (fun k j => ?_) Y.intPh1
  fin_cases k
  · exact double_multiplication_integral Y.B.G Y.intF n j
  · exact intS_X _
  · exact intS_X _

theorem first_partial_unit_constantCoeff (Y : FBChart C V O dd) (n : ℕ) : constantCoeff (p1 Y n) = 1 := by
  unfold p1
  rw [constantCoeff_ev (constant_zero_multiplication_triple Y n)]
  have h0 : Z0 (![0, pt C (n := 2) dd 0, pt C (n := 2) dd 1] : Fin 3 → Pt C 2 dd) := fun k j => by
    fin_cases k
    · exact map_zero _
    · exact z0_pt 0 j
    · exact z0_pt 1 j
  have := congrArg constantCoeff Y.B.cocycleLeft_zero_fst
  rw [constantCoeff_ev h0, map_one] at this
  exact this

end Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality

namespace Formalism.L2.FormalSeriesBounds

open FirstUnitSeriesIntegrality

theorem first_unit_series_integral : FirstUnitSeriesIntegral := by
  intro C _ _ V O _ _ dd Y
  have hP : IntS V (∏ i ∈ Finset.range (V.l - 1), p1 Y (i + 1)) :=
    Finset.prod_induction _ (IntS V) (fun a b ha hb => PartialDerivEval.intS_mul ha hb) PartialDerivEval.intS_one
      fun i _ => first_partial_unit_integral Y (i + 1)
  have hP0 : MvPowerSeries.constantCoeff (∏ i ∈ Finset.range (V.l - 1), p1 Y (i + 1)) = 1 := by
    rw [map_prod]; exact Finset.prod_eq_one fun i _ => first_partial_unit_constantCoeff Y (i + 1)
  exact intS_of_mul_eq_one (by rw [mul_comm]; exact second_coord_mul_inner Y) hP0 hP

end Formalism.L2.FormalSeriesBounds
