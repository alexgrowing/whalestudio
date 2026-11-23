import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdjointEndPairMemGaugedCurveLogarithms
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSet
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries

namespace GlobalTheory.RowLaw.GoodPair

variable {C : Type} [Field C]

section Val

variable {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_mul {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem mm_or {a b : C} (h : V.MM (a * b)) : V.MM a ∨ V.MM b := by
  unfold VF.MM at *
  rw [V.v.map_mul] at h
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  exact absurd h (not_lt.mpr (add_nonpos hc.1 hc.2))

theorem not_mm_one : ¬ V.MM (1 : C) := by
  unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl _

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_sum {ι : Type} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f V.MM (fun _ _ => mm_add) mm_zero h

theorem mm_of_pow {a : C} {n : ℕ} (h : V.MM (a ^ n)) : V.MM a := by
  induction n with
  | zero => exact absurd (by simpa using h) not_mm_one
  | succ n ih =>
    rw [pow_succ] at h
    exact (mm_or h).elim ih id

theorem ge_intCast (n : ℤ) : V.Ge 0 (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using VF.ge_natCast (V := V) m
  · simpa using (VF.ge_natCast (V := V) m).neg

theorem not_mm_natCast {k : ℕ} (h0 : 0 < k) (hk : k < V.l) : ¬ V.MM (k : C) := by
  intro h
  have hc : Nat.Coprime k V.l := (Nat.coprime_of_lt_prime h0.ne' hk V.l_prime).symm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (k : C) * (a : C) + (V.l : C) * (b : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    rw [← this]; ring
  exact not_mm_one (e ▸ mm_add (mm_mul h (ge_intCast a)) (mm_mul mm_l (ge_intCast b)))

end Val

section Ord

variable {τ : Type} {V : VF C}

theorem ordGe_mono {w : τ → ℕ} {m n : ℕ} (h : m ≤ n) {F : MvPowerSeries τ C} (hF : F ∈ ordGe C w n) :
    F ∈ ordGe C w m := fun e he => hF e (lt_of_lt_of_le he h)

theorem ordGe_pow' {w : τ → ℕ} {m : ℕ} {F : MvPowerSeries τ C} (hF : F ∈ ordGe C w m) (k : ℕ) :
    F ^ k ∈ ordGe C w (k * m) := by
  induction k with
  | zero => rw [zero_mul]; exact ordGe_zero _
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact ordGe_mul ih hF

theorem ordGe_scale {w : τ → ℕ} {n : ℕ} {m : ℕ} {F : MvPowerSeries τ C} (hF : F ∈ ordGe C w n) :
    F ∈ ordGe C (fun s => w s * m) (n * m) := by
  intro e he
  apply hF
  have : Finsupp.weight (fun s => w s * m) e = Finsupp.weight w e * m := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [this] at he
  exact lt_of_mul_lt_mul_right he (Nat.zero_le _)

theorem mvExp_sub {w : τ → ℕ} {m : ℕ} {f : MvPowerSeries τ C} (h0 : constantCoeff f = 0) (hf : f ∈ ordGe C w m) :
    mvExp f - 1 - f ∈ ordGe C w (2 * m) := by
  classical
  intro e he
  rw [map_sub, map_sub]
  show (∑ k ∈ Finset.range (e.degree + 1), coeff e (f ^ k) / (k.factorial : C)) - _ - _ = 0
  by_cases hne : e = 0
  · subst hne
    simp [h0]
  · have hd : e.degree ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff e).1 h)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hd
    rw [hn, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp
    · intro k _
      rw [ordGe_pow' hf (k + 1 + 1) e (lt_of_lt_of_le he (Nat.mul_le_mul_right _ (by omega))), zero_div]

theorem logInt_low [CharZero C] {w : τ → ℕ} {m : ℕ} {f : MvPowerSeries τ C} (hL : f ∈ logInt V τ)
    (hf : f ∈ ordGe C w m) (e : τ →₀ ℕ) (he : Finsupp.weight w e < 2 * m) : V.Ge 0 (coeff e f) := by
  have h := mvExp_sub hL.1 hf e he
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [← h]
  exact (hL.2 e).sub (GlobalTheory.RowVal.intS_one e)

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[simp] theorem ee_zero (i j : ℕ) : ee i j 0 = i := by simp [ee]
@[simp] theorem ee_one (i j : ℕ) : ee i j 1 = j := by simp [ee]

theorem eq_ee {e : Fin 2 →₀ ℕ} {i j : ℕ} (h0 : e 0 = i) (h1 : e 1 = j) : e = ee i j := by
  ext k
  fin_cases k <;> simp [h0, h1]

def wv (k : Fin 2) : Fin 2 → ℕ := fun i => if i = k then 1 else 0

theorem weight_wv (k : Fin 2) (e : Fin 2 →₀ ℕ) : Finsupp.weight (wv k) e = e k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [wv]

theorem coeff_mul_lead {F G : MvPowerSeries (Fin 2) C} {a b a' b' : ℕ} (hF : F ∈ ordGe C (wv 0) a)
    (hF' : F ∈ ordGe C (wv 1) b) (hG : G ∈ ordGe C (wv 0) a') (hG' : G ∈ ordGe C (wv 1) b') :
    coeff (ee (a + a') (b + b')) (F * G) = coeff (ee a b) F * coeff (ee a' b') G := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (ee a b, ee a' b')]
  · rintro ⟨e, e'⟩ he hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at he
    have h0 := congrArg (fun x => x 0) he
    have h1 := congrArg (fun x => x 1) he
    simp only [Finsupp.add_apply, ee_zero, ee_one] at h0 h1
    by_contra hc
    obtain ⟨hc1, hc2⟩ := mul_ne_zero_iff.1 hc
    have g1 : ¬ e 0 < a := fun h => hc1 (hF e (by rwa [weight_wv]))
    have g2 : ¬ e 1 < b := fun h => hc1 (hF' e (by rwa [weight_wv]))
    have g3 : ¬ e' 0 < a' := fun h => hc2 (hG e' (by rwa [weight_wv]))
    have g4 : ¬ e' 1 < b' := fun h => hc2 (hG' e' (by rwa [weight_wv]))
    exact hne (Prod.ext (eq_ee (by simp only; omega) (by simp only; omega))
      (eq_ee (by simp only; omega) (by simp only; omega)))
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (eq_ee (by simp) (by simp))) h

theorem coeff_pow_lead {F : MvPowerSeries (Fin 2) C} {a b : ℕ} (hF : F ∈ ordGe C (wv 0) a)
    (hF' : F ∈ ordGe C (wv 1) b) (n : ℕ) : coeff (ee (n * a) (n * b)) (F ^ n) = coeff (ee a b) F ^ n := by
  induction n with
  | zero =>
    have : ee (0 * a) (0 * b) = 0 := (eq_ee (by simp) (by simp)).symm
    rw [this]; simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul, Nat.succ_mul,
      coeff_mul_lead (ordGe_pow' hF n) (ordGe_pow' hF' n) hF hF', ih]

theorem logInt_frob [CharZero C] {p : ℕ} {f : MvPowerSeries (Fin 2) C} (hL : f ∈ logInt V (Fin 2))
    (hf : f ∈ ordGe C (wv 0) p) (hf' : f ∈ ordGe C (wv 1) 1)
    (h : V.MM ((V.l : C) * coeff (ee (V.l * p) V.l) f)) : V.MM (coeff (ee p 1) f) := by
  have hl := V.l_prime
  set F := mvExp f - 1 with hFdef
  have hFe : F = (mvExp f - 1 - f) + f := by rw [hFdef]; ring
  have hF : F ∈ ordGe C (wv 0) p := by
    rw [hFe]; exact Submodule.add_mem _ (ordGe_mono (by omega) (mvExp_sub hL.1 hf)) hf
  have hF' : F ∈ ordGe C (wv 1) 1 := by
    rw [hFe]; exact Submodule.add_mem _ (ordGe_mono (by omega) (mvExp_sub hL.1 hf')) hf'
  have hc : coeff (ee p 1) F = coeff (ee p 1) f := by
    rw [hFe, map_add, mvExp_sub hL.1 hf' _ (by rw [weight_wv]; simp), zero_add]
  have hFi : IntS V F := fun e => by
    rw [hFdef, map_sub]; exact (hL.2 e).sub (GlobalTheory.RowVal.intS_one e)
  have hF0 : constantCoeff F = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact hF' 0 (by simp)
  have hlog : PowerSeries.subst F (PowerSeries.log C) = f := by
    rw [hFdef, mvExp_eq_subst hL.1]; exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.log_exp hL.1
  rw [← hlog, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
    finsum_eq_sum_of_support_subset (s := Finset.range (V.l + 1)), Finset.sum_range_succ, mul_add] at h
  · have h1 : V.MM ((V.l : C) * ∑ k ∈ Finset.range V.l,
        PowerSeries.coeff k (PowerSeries.log C) • coeff (ee (V.l * p) V.l) (F ^ k)) := by
      rw [Finset.mul_sum]
      refine mm_sum _ fun k hk => ?_
      rw [PowerSeries.coeff_log]
      split_ifs with hk0
      · simpa using mm_zero
      · have hkc : (k : C) ≠ 0 := Nat.cast_ne_zero.2 hk0
        refine (mm_or (a := (k : C)) ?_).resolve_left
          (not_mm_natCast (Nat.pos_of_ne_zero hk0) (Finset.mem_range.1 hk))
        have hm := mm_mul (V := V) mm_l ((VF.Ge.one.neg.pow (k + 1)).mul_int
          (AddCurve.intS_pow hFi k (ee (V.l * p) V.l)))
        convert hm using 1
        simp only [smul_eq_mul, map_div₀, map_pow, map_neg, map_one, map_natCast]
        field_simp
    have h2 := mm_add h (mm_neg h1)
    rw [add_comm, neg_add_cancel_left, PowerSeries.coeff_log, if_neg hl.ne_zero] at h2
    have h3 := coeff_pow_lead hF hF' V.l
    rw [mul_one] at h3
    rw [h3, hc] at h2
    have h4 := mm_mul h2 (VF.Ge.one.neg.pow (V.l + 1))
    apply mm_of_pow (n := V.l)
    convert h4 using 1
    have hlc : (V.l : C) ≠ 0 := VF.l_ne_zero
    simp only [smul_eq_mul, map_div₀, map_pow, map_neg, map_one, map_natCast]
    field_simp
    rw [← pow_mul, mul_comm _ 2, pow_mul]
    simp
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hk'
    apply hk
    have h1 : V.l < k := by simpa using hk'
    rw [ordGe_pow hF' k _ (by rw [weight_wv]; simpa using h1), smul_zero]

end Ord

section Two

variable {V : VF C}

theorem coeff_mul_sep {F G : MvPowerSeries (Fin 2) C} (hF : ∀ e : Fin 2 →₀ ℕ, e 1 ≠ 0 → coeff e F = 0)
    (hG : ∀ e : Fin 2 →₀ ℕ, e 0 ≠ 0 → coeff e G = 0) (i j : ℕ) :
    coeff (ee i j) (F * G) = coeff (ee i 0) F * coeff (ee 0 j) G := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (ee i 0, ee 0 j)]
  · rintro ⟨e, e'⟩ he hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at he
    have h0 := congrArg (fun x => x 0) he
    have h1 := congrArg (fun x => x 1) he
    simp only [Finsupp.add_apply, ee_zero, ee_one] at h0 h1
    by_contra hc
    obtain ⟨hc1, hc2⟩ := mul_ne_zero_iff.1 hc
    have g1 : e 1 = 0 := by_contra fun h => hc1 (hF e h)
    have g2 : e' 0 = 0 := by_contra fun h => hc2 (hG e' h)
    exact hne (Prod.ext (eq_ee (by simp only; omega) (by simp only; omega))
      (eq_ee (by simp only; omega) (by simp only; omega)))
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (eq_ee (by simp) (by simp))) h

def ue (k : Fin 2) : Unit ↪ Fin 2 := ⟨fun _ => k, fun _ _ _ => rfl⟩

def em1 (k : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C := rename (ue k) (f : MvPowerSeries Unit C)

theorem coeff_single_powerSeriesInOneOfTwoVariables (k : Fin 2) (f : PowerSeries C) (n : ℕ) :
    coeff (Finsupp.single k n) (em1 k f) = PowerSeries.coeff n f := by
  have : Finsupp.single k n = Finsupp.embDomain (ue k) (Finsupp.single () n) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [this, em1, coeff_embDomain_rename]
  rfl

theorem coeff_powerSeriesInOneOfTwoVariables_other_ne {k j : Fin 2} (hj : j ≠ k) (f : PowerSeries C) (e : Fin 2 →₀ ℕ) (he : e j ≠ 0) :
    coeff e (em1 k f) = 0 := by
  apply coeff_rename_eq_zero
  rintro ⟨x, rfl⟩
  apply he
  apply Finsupp.mapDomain_notin_range
  rintro ⟨u, hu⟩
  exact hj hu.symm

theorem coeff_powerSeriesInOneOfTwoVariables_cases (k : Fin 2) (f : PowerSeries C) (e : Fin 2 →₀ ℕ) :
    coeff e (em1 k f) = 0 ∨ coeff e (em1 k f) = PowerSeries.coeff (e k) f := by
  by_cases h : ∃ j, j ≠ k ∧ e j ≠ 0
  · obtain ⟨j, hj, he⟩ := h
    exact Or.inl (coeff_powerSeriesInOneOfTwoVariables_other_ne hj f e he)
  · right
    push Not at h
    have : e = Finsupp.single k (e k) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp
      · rw [h j hj, Finsupp.single_eq_of_ne hj]
    conv_lhs => rw [this]
    exact coeff_single_powerSeriesInOneOfTwoVariables k f _

theorem ee_left (n : ℕ) : ee n 0 = Finsupp.single 0 n := by simp [ee]
theorem ee_right (n : ℕ) : ee 0 n = Finsupp.single 1 n := by simp [ee]

theorem constantCoeff_powerSeriesInOneOfTwoVariables (k : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (em1 k f) = 0 := by
  have := coeff_single_powerSeriesInOneOfTwoVariables k f 0
  rw [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  rw [this, hf]

theorem integral_powerSeriesInOneOfTwoVariables (k : Fin 2) {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) : IntS V (em1 k f) := by
  intro e
  rcases coeff_powerSeriesInOneOfTwoVariables_cases k f e with h | h <;> rw [h]
  · exact VF.Ge.zero 0
  · exact hf _

theorem powerSeriesInOneOfTwoVariables_mem_weightedOrderGe (k : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    em1 k f ∈ ordGe C (wv k) 1 := by
  intro e he
  rw [weight_wv] at he
  rcases coeff_powerSeriesInOneOfTwoVariables_cases k f e with h | h <;> rw [h]
  rw [show e k = 0 by omega, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

theorem subst_powerSeriesInOneOfTwoVariables_alongCurve (k : Fin 2) {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (F : MvPowerSeries σ C) :
    subst (fun i => em1 k (γ i)) F = em1 k (alongCv γ F) := by
  unfold em1 alongCv
  simp only [rename_eq_subst]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hγ) (HasSubst.X_comp _)]

def sc (k : Fin 2) (z : C) : Fin 2 → C := fun i => z ^ wv k i

theorem coeff_sc (k : Fin 2) (z : C) (F : MvPowerSeries (Fin 2) C) (e : Fin 2 →₀ ℕ) :
    coeff e (rescale (sc k z) F) = z ^ e k * coeff e F := by
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  fin_cases k <;> simp [sc, wv]

theorem rescale_other_powerSeriesInOneOfTwoVariables {k j : Fin 2} (hj : j ≠ k) (z : C) (f : PowerSeries C) : rescale (sc j z) (em1 k f) = em1 k f := by
  ext e
  rw [coeff_sc]
  by_cases he : e j = 0
  · rw [he, pow_zero, one_mul]
  · rw [coeff_powerSeriesInOneOfTwoVariables_other_ne hj f e he, mul_zero]

theorem coeff_trace {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (k : Fin 2)
    (F : MvPowerSeries (Fin 2) C) (e : Fin 2 →₀ ℕ) :
    coeff e (∑ j ∈ Finset.range l, rescale (sc k (ζ ^ j)) F) = if l ∣ e k then (l : C) * coeff e F else 0 := by
  simp only [map_sum, coeff_sc, ← Finset.sum_mul]
  split_ifs with hn
  · obtain ⟨q, hq⟩ := hn
    have : ∀ j, (ζ ^ j) ^ (e k) = 1 := fun j => by
      rw [hq, ← pow_mul, mul_left_comm, pow_mul, hζ.pow_eq_one, one_pow]
    simp [this]
  · have hc : (e k).Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
    have h0 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ (e k) = 0 := by
      rw [← (hζ.pow_of_coprime _ hc).geom_sum_eq_zero hl.one_lt]
      exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h0, zero_mul]

theorem trace_ord {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (k : Fin 2)
    {F : MvPowerSeries (Fin 2) C} (hF : F ∈ ordGe C (wv k) 1) :
    ∑ j ∈ Finset.range l, rescale (sc k (ζ ^ j)) F ∈ ordGe C (wv k) l := by
  intro e he
  rw [coeff_trace hl hζ]
  rw [weight_wv] at he
  split_ifs with h
  · rw [hF e (by rw [weight_wv, Nat.eq_zero_of_dvd_of_lt h he]; exact Nat.one_pos), mul_zero]
  · rfl

theorem trace_ord' {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (k : Fin 2) {w : Fin 2 → ℕ} {n : ℕ}
    {F : MvPowerSeries (Fin 2) C} (hF : F ∈ ordGe C w n) :
    ∑ j ∈ Finset.range l, rescale (sc k (ζ ^ j)) F ∈ ordGe C w n := by
  intro e he
  rw [coeff_trace hl hζ, hF e he]
  simp

theorem sc_const (r : Fin 2 → C) (s : Fin 2) :
    constantCoeff ((r • (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C)) s) = 0 := by
  simp

theorem sc_int (k : Fin 2) {z : C} (hz : V.Ge 0 z) (s : Fin 2) :
    IntS V ((sc k z • (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C)) s) := by
  intro e
  rw [Pi.smul_apply', coeff_smul]
  exact (hz.pow _).mul_int (intS_X s e)

end Two

section Gauge

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem subst_hAt (X : RawChart C d I κ) {ρ τ : Type} [Finite ρ] {a b : κ → MvPowerSeries ρ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) {c : ρ → MvPowerSeries τ C}
    (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (hAt X a b) = hAt X (fun i => subst c (a i)) (fun i => subst c (b i)) := by
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_pair ha hb) (hasSubst_of_constantCoeff_zero hc)]
  congr 1
  funext p
  split_ifs <;> rfl

theorem h_const (H : RLaw X V) : constantCoeff X.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact H.axes 0 0 (by simp)

theorem hAt_const (H : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) : constantCoeff (hAt X a b) = 0 :=
  constantCoeff_subst_zero (AddCurve.pair_const ha hb) (h_const H)

theorem hAt_sym [CharZero C] (H : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hai : ∀ i, IntS V (a i)) (hbi : ∀ i, IntS V (b i)) : hAt X b a - hAt X a b ∈ logInt V τ := by
  have hc := AddCurve.pair_const ha hb
  have hS := hasSubst_of_constantCoeff_zero hc
  have h := logInt_subst hc (fun p => by split_ifs; exacts [hai _, hbi _])
    (F := hAt X (gp C κ (1 : Fin 2)) (gp C κ 0) - X.h)
    ⟨by rw [map_sub, hAt_const H (gp_const _) (gp_const _), h_const H, sub_zero], H.sy⟩
  rw [subst_sub hS, subst_hAt X (gp_const _) (gp_const _) hc] at h
  simp only [gp, subst_X hS] at h
  exact h

theorem hAt_add [CharZero C] (H : RLaw X V) {τ : Type} {a a' b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ i, constantCoeff (a' i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hai : ∀ i, IntS V (a i)) (hai' : ∀ i, IntS V (a' i)) (hbi : ∀ i, IntS V (b i)) :
    hAt X a b + hAt X a' b - hAt X (addP X a a') b ∈ logInt V τ := by
  let c : Fin 3 × κ → MvPowerSeries τ C := fun p => ![a, a', b] p.1 p.2
  have hc : ∀ p, constantCoeff (c p) = 0 := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [ha x, ha' x, hb x]
  have hi : ∀ p, IntS V (c p) := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [hai x, hai' x, hbi x]
  have hS := hasSubst_of_constantCoeff_zero hc
  have hA := AddCurve.formalAdd_const H (gp_const (C := C) (κ := κ) (0 : Fin 3)) (gp_const 1)
  have h := logInt_subst hc hi
    (F := hAt X (gp C κ (0 : Fin 3)) (gp C κ 2) + hAt X (gp C κ 1) (gp C κ 2) -
      hAt X (addP X (gp C κ 0) (gp C κ 1)) (gp C κ 2))
    ⟨by rw [map_sub, map_add, hAt_const H (gp_const _) (gp_const _), hAt_const H (gp_const _) (gp_const _),
      hAt_const H hA (gp_const _), add_zero, sub_zero], H.ph1⟩
  rw [subst_sub hS, subst_add hS, subst_hAt X (gp_const _) (gp_const _) hc, subst_hAt X (gp_const _) (gp_const _) hc,
    subst_hAt X hA (gp_const _) hc] at h
  simp only [AddCurve.subst_addP H (gp_const (C := C) (κ := κ) (0 : Fin 3)) (gp_const 1) hc] at h
  simp only [gp, subst_X hS] at h
  exact h

theorem hAt_ord_left (H : RLaw X V) {τ : Type} {w : τ → ℕ} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, a i ∈ ordGe C w 1) :
    hAt X a b ∈ ordGe C w 1 := by
  refine ordGe_subst (w' := fun p => if p.1 = 0 then 1 else 0) (hasSubst_pair ha hb) (fun p => ?_) fun e he => ?_
  · split_ifs
    · exact hw _
    · exact ordGe_zero _
  · refine H.axes 0 e fun s hs h0 => ?_
    have := Finsupp.le_weight (fun p : Fin 2 × κ => if p.1 = 0 then 1 else 0) (s := s) (by simp [h0]) e
    have h2 := Finsupp.mem_support_iff.1 hs
    omega

theorem hAt_zero (H : RLaw X V) {τ : Type} {b : κ → MvPowerSeries τ C} (hb : ∀ i, constantCoeff (b i) = 0) :
    hAt X (fun _ => 0) b = 0 := by
  ext e
  exact hAt_ord_left H (w := fun _ => 0) (fun _ => map_zero _) hb (fun _ => Submodule.zero_mem _) e
    (by simp [Finsupp.weight_apply])

theorem exists_sum [CharZero C] (H : RLaw X V) {τ : Type} {a : ℕ → κ → MvPowerSeries τ C} {b : κ → MvPowerSeries τ C}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hai : ∀ j i, IntS V (a j i)) (hbi : ∀ i, IntS V (b i)) (n : ℕ) :
    ∃ S : κ → MvPowerSeries τ C, (∀ i, constantCoeff (S i) = 0) ∧ (∀ i, IntS V (S i)) ∧
      (∀ i, subst S (X.lg i) = ∑ j ∈ Finset.range n, subst (a j) (X.lg i)) ∧
      ∑ j ∈ Finset.range n, hAt X (a j) b - hAt X S b ∈ logInt V τ := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, fun _ => map_zero _, fun _ => intS_zero, fun i => ?_, ?_⟩
    · rw [Finset.sum_range_zero]
      exact AddCurve.subst_eq_zero_of_van (fun _ => map_zero _) (fun _ _ => rfl) (van_univ (lg_const H i))
    · rw [hAt_zero H hb]; simp
  | succ n ih =>
    obtain ⟨S, h0, hi, hl, hh⟩ := ih
    refine ⟨addP X S (a n), AddCurve.formalAdd_const H h0 (ha n), AddCurve.intS_addP H h0 (ha n) hi (hai n),
      fun i => ?_, ?_⟩
    · rw [AddCurve.lg_addP H h0 (ha n), hl, Finset.sum_range_succ]
    · have := add_mem hh (hAt_add H h0 (ha n) hb hi (hai n) hbi)
      rw [Finset.sum_range_succ]
      convert this using 1
      ring

theorem ord_of_lg (H : RLaw X V) {τ : Type} {w : τ → ℕ} {m : ℕ} {b : κ → MvPowerSeries τ C}
    (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, subst b (X.lg i) ∈ ordGe C w m) (i : κ) : b i ∈ ordGe C w m := by
  have hB := hasSubst_of_constantCoeff_zero hb
  have e : b i = subst (fun j => subst b (X.lg j)) (X.ex i) := by
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const H)) hB, H.exlg, subst_X hB]
  rw [e]
  have := ordGe_subst (w := w) (w' := fun _ : κ => 1 * m)
    (hasSubst_of_constantCoeff_zero fun j => constantCoeff_subst_zero hb (lg_const H j))
    (fun j => by rw [one_mul]; exact hw j) (ordGe_scale (m := m) (ordGe_one_of_const (H.exc i)))
  rwa [one_mul] at this

theorem hAt_lin (H : RLaw X V) {τ : Type} {w : τ → ℕ} {m : ℕ} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hw : ∀ i, subst b (X.lg i) ∈ ordGe C w m) :
    hAt X a b - ∑ j, subst b (X.lg j) * subst a (dz j X.h) ∈ ordGe C w (2 * m) := by
  have hw' := ord_of_lg H hb hw
  have hB := hasSubst_of_constantCoeff_zero hb
  have h1 : ∀ i, subst b (X.lg i) - b i ∈ ordGe C w (2 * m) := fun i => by
    have h : X.lg i - MvPowerSeries.X i ∈ ordGe C (fun _ : κ => 1) 2 := by
      intro e he
      rw [weight_one] at he
      rw [map_sub, H.lin i e (by omega), sub_self]
    have := ordGe_subst hB (fun j => by rw [one_mul]; exact hw' j) (ordGe_scale (m := m) h)
    rwa [subst_sub hB, subst_X hB] at this
  have hP := hasSubst_pair ha hb
  have h2 : hAt X a b - ∑ j, b j * subst a (dz j X.h) ∈ ordGe C w (2 * m) := by
    have := ordGe_subst (w := w) hP (fun p => by
      obtain ⟨g, x⟩ := p
      fin_cases g
      · simpa [wz] using ordGe_zero _
      · simpa [wz] using hw' x) (ordGe_scale (m := m) (taylor (h_ord H)))
    rw [subst_sub hP, ← coe_substAlgHom hP, map_sum] at this
    convert this using 2
    · rw [coe_substAlgHom hP]; rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, coe_substAlgHom hP, subst_X hP, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hP]
      congr 1
      congr 1
      funext x
      rw [Function.comp_apply, subst_X hP]
      rfl
  have h3 : ∑ j, (subst b (X.lg j) - b j) * subst a (dz j X.h) ∈ ordGe C w (2 * m) :=
    Submodule.sum_mem _ fun j _ => ordGe_mul (h1 j) (ordGe_zero _)
  have h4 := Submodule.sub_mem _ h2 h3
  simp only [sub_mul, Finset.sum_sub_distrib] at h4
  convert h4 using 1
  ring

theorem hAt_ord_lg (H : RLaw X V) {τ : Type} {w : τ → ℕ} {m : ℕ} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hw : ∀ i, subst b (X.lg i) ∈ ordGe C w m) : hAt X a b ∈ ordGe C w m := by
  have h := Submodule.add_mem _ (ordGe_mono (by omega : m ≤ 2 * m) (hAt_lin H ha hb hw))
    (Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) => ordGe_mul (hw j) (ordGe_zero (subst a (dz j X.h))))
  rwa [sub_add_cancel] at h

theorem exists_trace [CharZero C] (H : RLaw X V) {ζ : C} (hζ : V.Ge 0 ζ) (k : Fin 2) (n : ℕ)
    {a b : κ → MvPowerSeries (Fin 2) C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hai : ∀ i, IntS V (a i)) (hbi : ∀ i, IntS V (b i)) (hbk : ∀ z i, rescale (sc k z) (b i) = b i) :
    ∃ S : κ → MvPowerSeries (Fin 2) C, (∀ i, constantCoeff (S i) = 0) ∧
      (∀ i, subst S (X.lg i) = ∑ j ∈ Finset.range n, rescale (sc k (ζ ^ j)) (subst a (X.lg i))) ∧
      ∑ j ∈ Finset.range n, rescale (sc k (ζ ^ j)) (hAt X a b) - hAt X b S ∈ logInt V (Fin 2) ∧
      ∑ j ∈ Finset.range n, rescale (sc k (ζ ^ j)) (hAt X b a) - hAt X b S ∈ logInt V (Fin 2) := by
  have ha' : ∀ j i, constantCoeff (rescale (sc k (ζ ^ j)) (a i)) = 0 := fun j i => by
    rw [rescale_eq_subst]; exact constantCoeff_subst_zero (sc_const _) (ha i)
  have hai' : ∀ j i, IntS V (rescale (sc k (ζ ^ j)) (a i)) := fun j i => by
    rw [rescale_eq_subst]; exact GlobalTheory.RowVal.intS_subst (sc_const _) (sc_int k (hζ.pow j)) (hai i)
  obtain ⟨S, h0, hi, hl, hh⟩ := exists_sum H (a := fun j i => rescale (sc k (ζ ^ j)) (a i)) ha' hb hai' hbi n
  have e1 : ∀ j, rescale (sc k (ζ ^ j)) (hAt X a b) = hAt X (fun i => rescale (sc k (ζ ^ j)) (a i)) b := fun j => by
    rw [rescale_eq_subst, subst_hAt X ha hb (sc_const _)]
    simp only [← rescale_eq_subst, hbk]
  have e2 : ∀ j, rescale (sc k (ζ ^ j)) (hAt X b a) = hAt X b (fun i => rescale (sc k (ζ ^ j)) (a i)) := fun j => by
    rw [rescale_eq_subst, subst_hAt X hb ha (sc_const _)]
    simp only [← rescale_eq_subst, hbk]
  have k1 : ∑ j ∈ Finset.range n, rescale (sc k (ζ ^ j)) (hAt X a b) - hAt X b S ∈ logInt V (Fin 2) := by
    have := add_mem hh (hAt_sym H hb h0 hbi hi)
    simp only [e1]
    convert this using 1
    ring
  refine ⟨S, h0, fun i => ?_, k1, ?_⟩
  · rw [hl]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [rescale_eq_subst]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_of_constantCoeff_zero (sc_const _))]
  · have := add_mem k1 (sum_mem fun j (_ : j ∈ Finset.range n) => hAt_sym H (ha' j) hb (hai' j) hbi)
    simp only [e1, Finset.sum_sub_distrib] at this
    simp only [e2]
    convert this using 1
    ring

end Gauge

section Core

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem core (H : RLaw X V) {γ γ' : κ → PowerSeries C} (hγ : IsCv V γ) (hγ' : IsCv V γ')
    (hA : ∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0)
    (hB : ∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ' (X.lg i)) = 0)
    (hM : V.MM ((V.l : C) * ∑ j, ((V.l : C) * PowerSeries.coeff (V.l * V.l) (alongCv γ (X.lg j))) *
      PowerSeries.coeff V.l (alongCv γ' (dz j X.h)))) :
    V.MM ((V.l : C) * ∑ j, PowerSeries.coeff 1 (alongCv γ' (X.lg j)) *
      PowerSeries.coeff V.l (alongCv γ (dz j X.h))) := by
  haveI := H.charZero
  haveI := H.closed
  have hl := V.l_prime
  have hl2 := hl.two_le
  have hll : V.l + 1 ≤ V.l * V.l := by nlinarith
  haveI : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  haveI : NeZero V.l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have hζi : V.Ge 0 ζ := FrobCurve.ge_zero_of_pow_eq_one V hl.pos hζ.pow_eq_one
  have hγ0 := fun i => (hγ i).1
  have hγ0' := fun i => (hγ' i).1
  set a : κ → MvPowerSeries (Fin 2) C := fun i => em1 0 (γ i) with hadef
  set b : κ → MvPowerSeries (Fin 2) C := fun i => em1 1 (γ' i) with hbdef
  have ha : ∀ i, constantCoeff (a i) = 0 := fun i => constantCoeff_powerSeriesInOneOfTwoVariables 0 (hγ0 i)
  have hb : ∀ i, constantCoeff (b i) = 0 := fun i => constantCoeff_powerSeriesInOneOfTwoVariables 1 (hγ0' i)
  have hai : ∀ i, IntS V (a i) := fun i => integral_powerSeriesInOneOfTwoVariables 0 (hγ i).2
  have hbi : ∀ i, IntS V (b i) := fun i => integral_powerSeriesInOneOfTwoVariables 1 (hγ' i).2
  have hao : ∀ i, a i ∈ ordGe C (wv 0) 1 := fun i => powerSeriesInOneOfTwoVariables_mem_weightedOrderGe 0 (hγ0 i)
  have hbo : ∀ i, b i ∈ ordGe C (wv 1) 1 := fun i => powerSeriesInOneOfTwoVariables_mem_weightedOrderGe 1 (hγ0' i)
  have hsa : ∀ F, subst a F = em1 0 (alongCv γ F) := subst_powerSeriesInOneOfTwoVariables_alongCurve 0 hγ0
  have hsb : ∀ F, subst b F = em1 1 (alongCv γ' F) := subst_powerSeriesInOneOfTwoVariables_alongCurve 1 hγ0'
  have hB0 := hAt_ord_left H ha hb hao
  have hB1 := hAt_ord H ha hb hbo
  have hord : ∀ (k : Fin 2) (f : PowerSeries C), (∀ n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n f = 0) →
      ∑ j ∈ Finset.range V.l, rescale (sc k (ζ ^ j)) (em1 k f) ∈ ordGe C (wv k) (V.l * V.l) := by
    intro k f hf e he
    rw [weight_wv] at he
    rw [coeff_trace hl hζ]
    split_ifs with hd
    · rcases coeff_powerSeriesInOneOfTwoVariables_cases k f e with h | h
      · rw [h, mul_zero]
      · rw [h, hf _ hd he, mul_zero]
    · rfl

  obtain ⟨S', hS0', hSl', -, hSh'⟩ := exists_trace H hζi 1 V.l hb ha hbi hai fun z i => rescale_other_powerSeriesInOneOfTwoVariables (by decide) z _
  have hS'o : hAt X a S' ∈ ordGe C (wv 1) (V.l * V.l) :=
    hAt_ord_lg H ha hS0' fun i => by rw [hSl', hsb]; exact hord 1 _ (hB i)
  have g21 : V.Ge 0 ((V.l : C) * coeff (ee (V.l * V.l) V.l) (hAt X a b)) := by
    have := logInt_low hSh' (Submodule.sub_mem _ (trace_ord hl hζ 1 hB1) (ordGe_mono (by omega) hS'o))
      (ee (V.l * V.l) V.l) (by rw [weight_wv, ee_one]; omega)
    rwa [map_sub, coeff_trace hl hζ, if_pos (by simp), hS'o _ (by rw [weight_wv, ee_one]; omega), sub_zero] at this

  obtain ⟨S, hS0, hSl, hSh, -⟩ := exists_trace H hζi 0 V.l ha hb hai hbi fun z i => rescale_other_powerSeriesInOneOfTwoVariables (by decide) z _
  have hSlo : ∀ i, subst S (X.lg i) ∈ ordGe C (wv 0) (V.l * V.l) := fun i => by
    rw [hSl, hsa]; exact hord 0 _ (hA i)
  have hSo : hAt X b S ∈ ordGe C (wv 0) (V.l * V.l) := hAt_ord_lg H hb hS0 hSlo
  have hG : coeff (ee (V.l * V.l) V.l) (hAt X b S) =
      ∑ j, ((V.l : C) * PowerSeries.coeff (V.l * V.l) (alongCv γ (X.lg j))) *
        PowerSeries.coeff V.l (alongCv γ' (dz j X.h)) := by
    have := hAt_lin H hb hS0 hSlo (ee (V.l * V.l) V.l) (by rw [weight_wv, ee_zero]; omega)
    rw [map_sub, sub_eq_zero, map_sum] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hSl, hsa, hsb, coeff_mul_sep _ (fun e he => coeff_powerSeriesInOneOfTwoVariables_other_ne (by decide) _ e he), coeff_trace hl hζ,
      if_pos (by simp), ee_left, ee_right, coeff_single_powerSeriesInOneOfTwoVariables, coeff_single_powerSeriesInOneOfTwoVariables]
    intro e he
    rw [coeff_trace hl hζ, coeff_powerSeriesInOneOfTwoVariables_other_ne (by decide) _ e he]
    simp
  have hc : coeff (ee V.l 1) (hAt X a b) = ∑ j, PowerSeries.coeff 1 (alongCv γ' (X.lg j)) *
      PowerSeries.coeff V.l (alongCv γ (dz j X.h)) := by
    have := hAt_lin H (w := wv 1) (m := 1) ha hb
      (fun i => by rw [hsb]; exact powerSeriesInOneOfTwoVariables_mem_weightedOrderGe 1 (constantCoeff_subst_zero (τ := Unit) hγ0' (lg_const H i)))
      (ee V.l 1) (by rw [weight_wv, ee_one]; omega)
    rw [map_sub, sub_eq_zero, map_sum] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsa, hsb, mul_comm, coeff_mul_sep (fun e he => coeff_powerSeriesInOneOfTwoVariables_other_ne (by decide) _ e he)
      (fun e he => coeff_powerSeriesInOneOfTwoVariables_other_ne (by decide) _ e he), ee_left, ee_right, coeff_single_powerSeriesInOneOfTwoVariables, coeff_single_powerSeriesInOneOfTwoVariables, mul_comm]
  have key := logInt_frob (p := V.l) hSh
    (Submodule.sub_mem _ (trace_ord hl hζ 0 hB0) (ordGe_mono (by omega) hSo))
    (Submodule.sub_mem _ (trace_ord' hl hζ 0 hB1) (hAt_ord_left H hb hS0 hbo)) (by
      rw [map_sub, coeff_trace hl hζ, if_pos (by simp), hG, mul_sub, sub_eq_add_neg]
      exact mm_add (mm_mul mm_l g21) (mm_neg hM))
  rwa [map_sub, coeff_trace hl hζ, if_pos (by simp), hSo _ (by rw [weight_wv, ee_zero]; omega), sub_zero, hc] at key

theorem coeff_sg (X : RawChart C d I κ) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (v : κ → C) (n : ℕ) :
    PowerSeries.coeff n (alongCv γ (X.sg v)) = -∑ j, v j * PowerSeries.coeff n (alongCv γ (dz j X.h)) := by
  have hS : HasSubst γ := hasSubst_of_constantCoeff_zero (τ := Unit) hγ
  have : alongCv γ (X.sg v) = -∑ j, v j • alongCv γ (dz j X.h) := by
    unfold alongCv
    rw [CvEnd.sg_eq, ← CvEnd.subst_sum_smul hS, ← coe_substAlgHom hS, map_neg]
  rw [this, map_neg, map_sum]
  simp only [PowerSeries.coeff_smul, smul_eq_mul]

theorem good_curve [NeZero d] {g : Fin 2} (H : X.CartHyp V g) {a : ZMod d} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (hx : (RawChart.cart H).Good a w x) :
    ∃ γ : κ → PowerSeries C, IsCv V γ ∧
      (∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) ∧
      (∀ i, PowerSeries.coeff 1 (alongCv γ (X.lg i)) = ∑ c, X.u g c i * w c) ∧
      (∀ i, (V.l : C) * PowerSeries.coeff (V.l * V.l) (alongCv γ (X.lg i)) =
        ∑ c, X.u g c i * (RawChart.cart H).V2 x c) ∧
      ∀ q : I (1 - g), ∃ z, V.Ge 0 z ∧ (V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg (X.u (1 - g) q))) =
        (V.l : C) * z - (RawChart.cart H).c0' x q := by
  have hl := V.l_prime
  have hl2 := hl.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ : x ∈ X.TySet V g := hx.1.1
  have c0 : ∀ y : ℕ → C, PowerSeries.coeff 1 (tyS V.l y) = y 0 := fun y => by
    simpa using coeff_tyS_pow hl2 y 0
  have c1 : ∀ y : ℕ → C, PowerSeries.coeff V.l (tyS V.l y) = y 1 := fun y => by
    simpa using coeff_tyS_pow hl2 y 1
  have c2 : ∀ y : ℕ → C, PowerSeries.coeff (V.l * V.l) (tyS V.l y) = y 2 := fun y => by
    simpa [pow_two] using coeff_tyS_pow hl2 y 2
  refine ⟨γ, hγ, fun i n hd hn => ?_, fun i => ?_, fun i => ?_, fun q => ⟨_, (hlam q).2 V.l, ?_⟩⟩
  · rw [h1, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [PowerSeries.coeff_smul]
    by_cases hs : ∃ s, V.l ^ s = n
    · obtain ⟨s, rfl⟩ := hs
      have hs2 : s < 2 := by
        rw [← pow_two] at hn
        exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 hn
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hl.one_lt.ne' (Nat.dvd_one.1 (by simpa using hd))
      rw [show s = 1 by omega, coeff_tyS_pow hl2, hx.2 c, smul_zero]
    · push Not at hs
      rw [coeff_tyS_of_ne _ _ hs, smul_zero]
  · rw [h1, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, c0, hx.1.2.1]
    rfl
  · rw [h1, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, c2, smul_eq_mul, Cart.V2]
    ring
  · have e := congrArg (PowerSeries.coeff V.l) (h2 q)
    rw [c1, map_add, map_sub, map_sum, Finset.sum_eq_zero, add_zero] at e
    · rw [Cart.c0', e]; ring
    · intro c _
      split_ifs
      · rw [PowerSeries.coeff_smul, c1, hx.2 c, smul_zero]
      · exact map_zero _

theorem forall_u_of_eq {g g' : Fin 2} (h : g' = g) (P : (κ → C) → Prop) (hP : ∀ q : I g', P (X.u g' q)) (c : I g) :
    P (X.u g c) := by
  subst h
  exact hP c

end Core

end GlobalTheory.RowLaw.GoodPair

open GlobalTheory.RowLaw.GoodPair in

theorem GlobalTheory.RowLaw.good_pairing_mem_max : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (g : Fin 2) (a a' : ZMod d) (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C) (w' : I (1 - g) → C) (x' : ℕ → I (1 - g) ⊕ JJ I (1 - g) → C), (RawChart.cart (H g)).Good a w x → (RawChart.cart (H (1 - g))).Good a' w' x' → (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) → V.MM (∑ q : I (1 - g), (RawChart.cart (H g)).c0' x q * w' q) := by
  intro C _ V d _ I _ κ _ X hX H g a a' w x w' x' hx hx' hV
  obtain ⟨γ, hγ, hA, -, hA2, hσ⟩ := good_curve (H g) hx
  obtain ⟨γ', hγ', hB, hB1, -, hσ'⟩ := good_curve (H (1 - g)) hx'
  have hγ0 := fun i => (hγ i).1
  have hγ0' := fun i => (hγ' i).1
  have hw' : ∀ q, V.Ge 0 (w' q) := fun q => by
    have := (RawChart.cart (H (1 - g))).bound0 0 x' hx'.1.1 (Sum.inl q)
    rw [hx'.1.2.1] at this
    simpa using this
  have hσ2 : ∀ c : I g, V.Ge 0 ((V.l : C) * PowerSeries.coeff V.l (alongCv γ' (X.sg (X.u g c)))) :=
    forall_u_of_eq (g' := 1 - (1 - g)) (by simp)
      (fun v => V.Ge 0 ((V.l : C) * PowerSeries.coeff V.l (alongCv γ' (X.sg v)))) fun q => by
        obtain ⟨z, hz, e⟩ := hσ' q
        rw [e]
        exact ((VF.ge_natCast _).mul_int hz).sub (hx'.c0'_int q)
  have key := core hX hγ hγ' hA hB (by
    have := mm_neg (mm_sum Finset.univ fun c _ => mm_mul (hV c) (hσ2 c))
    convert this using 1
    simp only [hA2, coeff_sg X hγ0', Finset.sum_mul, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring)
  choose z hz hz' using hσ
  have h2 := mm_add key (mm_sum Finset.univ fun q _ => mm_mul (mm_mul mm_l (hz q)) (hw' q))
  convert h2 using 1
  have e : ∀ q, (RawChart.cart (H g)).c0' x q =
      (V.l : C) * z q - (V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg (X.u (1 - g) q))) := fun q => by
    rw [hz' q]; ring
  simp only [e, hB1, coeff_sg X hγ0, Finset.sum_mul, Finset.mul_sum, mul_neg, sub_neg_eq_add, add_mul,
    Finset.sum_add_distrib]
  rw [add_comm, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring
