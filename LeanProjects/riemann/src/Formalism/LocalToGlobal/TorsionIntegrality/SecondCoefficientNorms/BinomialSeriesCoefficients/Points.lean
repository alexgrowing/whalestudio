import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

namespace Pts

open IntegralMvPolynomialLemmas

section Toolkit

variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}

theorem hasSubst {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx

theorem subst_subst {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0)
    {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) (f : PowerSeries K) :
    PowerSeries.subst x (PowerSeries.subst g f) = PowerSeries.subst (PowerSeries.subst x g) f :=
  PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
    (hasSubst hx) f

theorem substMv_subst {τ : Type} [Finite σ] {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) =
      PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def]
  exact MvPowerSeries.subst_comp_subst_apply (hasSubst hg).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f

theorem constantCoeff_subst {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx f hf

theorem constantCoeff_subst_l (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x l) = 0 :=
  constantCoeff_subst hx h.1

theorem constantCoeff_subst_linv (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x linv) = 0 :=
  constantCoeff_subst hx h.2.2.1

theorem subst_l_linv (h : IsLogPair l linv) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) l = g := by
  rw [← subst_subst h.2.2.1 hg, h.2.2.2.2, PowerSeries.subst_X (hasSubst hg)]

theorem subst_linv_l (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (PowerSeries.subst x l) linv = x := by
  rw [← subst_subst h.1 hx, h.2.2.2.1, PowerSeries.subst_X (hasSubst hx)]

theorem constantCoeff_add_l (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst x l + PowerSeries.subst y l) = 0 := by
  rw [map_add, constantCoeff_subst_l h hx, constantCoeff_subst_l h hy, add_zero]

theorem constantCoeff_C_mul_l (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.C a * PowerSeries.subst x l) = 0 := by
  rw [map_mul, constantCoeff_subst_l h hx, mul_zero]

theorem constantCoeff_sum_l (h : IsLogPair l linv) {n : Type} [Fintype n] (c : n → K)
    {u : n → MvPowerSeries σ K} (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => constantCoeff_C_mul_l h (c j) (hu j)

theorem constantCoeff_fadd (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (fadd l linv x y) = 0 :=
  constantCoeff_subst_linv h (constantCoeff_add_l h hx hy)

theorem constantCoeff_fmul (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (fmul l linv a x) = 0 :=
  constantCoeff_subst_linv h (constantCoeff_C_mul_l h a hx)

theorem constantCoeff_flin (h : IsLogPair l linv) {n : Type} [Fintype n] (c : n → K)
    {u : n → MvPowerSeries σ K} (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (flin l linv c u) = 0 :=
  constantCoeff_subst_linv h (constantCoeff_sum_l h c hu)

theorem l_fadd (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (fadd l linv x y) l = PowerSeries.subst x l + PowerSeries.subst y l :=
  subst_l_linv h (constantCoeff_add_l h hx hy)

theorem l_fmul (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (fmul l linv a x) l = MvPowerSeries.C a * PowerSeries.subst x l :=
  subst_l_linv h (constantCoeff_C_mul_l h a hx)

theorem l_flin (h : IsLogPair l linv) {n : Type} [Fintype n] (c : n → K)
    {u : n → MvPowerSeries σ K} (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    PowerSeries.subst (flin l linv c u) l =
      ∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l :=
  subst_l_linv h (constantCoeff_sum_l h c hu)

theorem fmul_fmul (h : IsLogPair l linv) (a b : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fmul l linv a (fmul l linv b x) = fmul l linv (a * b) x := by
  rw [fmul, l_fmul h b hx, fmul, map_mul, mul_assoc]

theorem fmul_one (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : fmul l linv 1 x = x := by
  rw [fmul, map_one, one_mul, subst_linv_l h hx]

theorem fmul_zero_left (h : IsLogPair l linv) (x : MvPowerSeries σ K) : fmul l linv 0 x = 0 := by
  rw [fmul, map_zero, zero_mul, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1]

theorem constantCoeff_mulBy (h : IsLogPair l linv) (a : K) :
    PowerSeries.constantCoeff (mulBy l linv a) = 0 := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  exact constantCoeff_subst h0 h.2.2.1

theorem fmul_eq_subst_mulBy (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fmul l linv a x = PowerSeries.subst x (mulBy l linv a) := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  rw [mulBy, subst_subst h0 hx, PowerSeries.subst_mul (hasSubst hx), PowerSeries.subst_C, fmul]

theorem mulBy_eq_fmul (a : K) : mulBy l linv a = fmul l linv a (PowerSeries.X : PowerSeries K) := by
  rw [fmul, PowerSeries.X_subst]
  rfl

theorem fadd_comm (x y : MvPowerSeries σ K) : fadd l linv x y = fadd l linv y x := by
  rw [fadd, fadd, add_comm]

theorem fadd_zero (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : fadd l linv x 0 = x := by
  rw [fadd, PowerSeries.subst_zero_of_constantCoeff_zero h.1, add_zero, subst_linv_l h hx]

theorem zero_fadd (h : IsLogPair l linv) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) : fadd l linv 0 x = x := by
  rw [fadd_comm, fadd_zero h hx]

theorem fmul_fadd (h : IsLogPair l linv) (a : K) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    fmul l linv a (fadd l linv x y) = fadd l linv (fmul l linv a x) (fmul l linv a y) := by
  rw [fmul, l_fadd h hx hy, fadd, l_fmul h a hx, l_fmul h a hy, mul_add]

theorem fmul_add (h : IsLogPair l linv) (a b : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fmul l linv (a + b) x = fadd l linv (fmul l linv a x) (fmul l linv b x) := by
  rw [fadd, l_fmul h a hx, l_fmul h b hx, fmul, map_add, add_mul]

theorem fadd_fmul_neg (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    fadd l linv (fmul l linv a x) (fmul l linv (-a) x) = 0 := by
  rw [← fmul_add h a (-a) hx, add_neg_cancel, fmul_zero_left h]

theorem addDefect_comm (ph : PowerSeries K) (x y : MvPowerSeries σ K) :
    be0 l linv ph x y = be0 l linv ph y x := by
  rw [be0, be0, fadd_comm]
  ring

theorem fadd_eq_substMv (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    fadd l linv x y = MvPowerSeries.subst ![x, y]
      (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) := by
  have ha : ∀ s : Fin 2, MvPowerSeries.constantCoeff (![x, y] s) = 0 := by
    intro s
    fin_cases s
    · exact hx
    · exact hy
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  rw [fadd, fadd, substMv_subst (constantCoeff_add_l h h0 h1) ha, MvPowerSeries.subst_add hs,
    substMv_subst h0 ha, substMv_subst h1 ha, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  rfl

theorem coeff_one_linv (h : IsLogPair l linv) : PowerSeries.coeff 1 linv = 1 := by
  have hc := coeff_subst_congr (g := linv)
    (h := PowerSeries.C (PowerSeries.coeff 1 linv) * PowerSeries.X) (a := l) h.1
    (Finsupp.single () 1) (fun k hk => by
      rw [Finsupp.degree_single] at hk
      interval_cases k
      · simp [h.2.2.1]
      · simp)
  rw [h.2.2.2.1, PowerSeries.subst_mul (hasSubst h.1), PowerSeries.subst_C,
    PowerSeries.subst_X (hasSubst h.1)] at hc
  have h1 : PowerSeries.coeff 1 (PowerSeries.X : PowerSeries K) =
      PowerSeries.coeff 1 (PowerSeries.C (PowerSeries.coeff 1 linv) * l) := hc
  rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul, h.2.1, mul_one] at h1
  exact h1.symm

end Toolkit

section Integral

variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}

theorem intMv_of_intPS {f : PowerSeries K} (hf : IntPS R f) : IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have : n = Finsupp.single () (n ()) := by
    ext
    simp
  rw [this]
  exact hf (n ())

theorem intPS_of_intMv {f : PowerSeries K} (hf : IntMv R (f : MvPowerSeries Unit K)) : IntPS R f :=
  fun n => hf (Finsupp.single () n)

theorem intMv_X (s : σ) : IntMv R (MvPowerSeries.X s : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem isPt_fadd (h : IsLogPair l linv) (hF : FGInt R l linv) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) : IsPt R (fadd l linv x y) := by
  refine ⟨constantCoeff_fadd h hx.1 hy.1, ?_⟩
  rw [fadd_eq_substMv h hx.1 hy.1]
  refine intMv_substMv hF fun s => ?_
  fin_cases s
  · exact hx
  · exact hy

theorem isPt_fmul (h : IsLogPair l linv) {a : K} (ha : EndInt R l linv a) {x : MvPowerSeries σ K}
    (hx : IsPt R x) : IsPt R (fmul l linv a x) := by
  refine ⟨constantCoeff_fmul h a hx.1, ?_⟩
  rw [fmul_eq_subst_mulBy h a hx.1]
  exact intMv_subst ha hx

theorem isPt_X : IsPt R (PowerSeries.X : MvPowerSeries Unit K) :=
  ⟨PowerSeries.constantCoeff_X, intMv_X ()⟩

theorem endInt_zero (h : IsLogPair l linv) : EndInt R l linv 0 := by
  intro n
  rw [mulBy_eq_fmul, fmul_zero_left h, map_zero]
  exact R.zero_mem

theorem endInt_one (h : IsLogPair l linv) : EndInt R l linv 1 := by
  unfold EndInt
  rw [mulBy_eq_fmul, fmul_one h PowerSeries.constantCoeff_X]
  exact intPS_of_intMv isPt_X.2

theorem endInt_add (h : IsLogPair l linv) (hF : FGInt R l linv) {a b : K}
    (ha : EndInt R l linv a) (hb : EndInt R l linv b) : EndInt R l linv (a + b) := by
  unfold EndInt
  rw [mulBy_eq_fmul, fmul_add h a b PowerSeries.constantCoeff_X]
  exact intPS_of_intMv (isPt_fadd h hF (isPt_fmul h ha isPt_X) (isPt_fmul h hb isPt_X)).2

theorem endInt_mul (h : IsLogPair l linv) {a b : K}
    (ha : EndInt R l linv a) (hb : EndInt R l linv b) : EndInt R l linv (a * b) := by
  unfold EndInt
  rw [mulBy_eq_fmul, ← fmul_fmul h a b PowerSeries.constantCoeff_X]
  exact intPS_of_intMv (isPt_fmul h ha (isPt_fmul h hb isPt_X)).2

theorem coeff_substMv_two {τ : Type} (F : MvPowerSeries (Fin 2) K) {a : Fin 2 → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a F) =
      finsum fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d F * MvPowerSeries.coeff e (a 0 ^ d 0 * a 1 ^ d 1) := by
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]

theorem coeff_law_of_zero (h : IsLogPair l linv) (d : Fin 2 →₀ ℕ) (hd : d 0 = 0) :
    MvPowerSeries.coeff d
        (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) := by
  classical
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have ha : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) s) = 0 := by
    intro s
    fin_cases s
    · exact map_zero _
    · exact hX
  have key := coeff_substMv_two
    (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ha
    (Finsupp.single () (d 1))
  rw [← fadd_eq_substMv h (map_zero _) hX, zero_fadd h hX, finsum_eq_single _ d] at key
  · have e1 : MvPowerSeries.coeff (Finsupp.single () (d 1))
        ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d 0 *
          (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 1 ^ d 1) = 1 := by
      rw [hd, pow_zero, one_mul]
      exact PowerSeries.coeff_X_pow_self (d 1)
    rw [e1, mul_one] at key
    rw [← key, MvPowerSeries.coeff_X]
    have e2 : MvPowerSeries.coeff (Finsupp.single () (d 1)) (PowerSeries.X : MvPowerSeries Unit K) =
        if d 1 = 1 then 1 else 0 := PowerSeries.coeff_X (d 1)
    rw [e2]
    congr 1
    apply propext
    constructor
    · intro h1
      ext s
      fin_cases s
      · simpa using hd
      · simpa using h1
    · intro h1
      rw [h1]
      simp
  · intro d' hd'
    by_cases h0 : d' 0 = 0
    · have h1 : d' 1 ≠ d 1 := by
        intro h1
        apply hd'
        ext s
        fin_cases s
        · simpa [hd] using h0
        · simpa using h1
      have e1 : MvPowerSeries.coeff (Finsupp.single () (d 1))
          ((![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d' 0 *
            (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 1 ^ d' 1) = 0 := by
        rw [h0, pow_zero, one_mul]
        have := PowerSeries.coeff_X_pow (R := K) (d 1) (d' 1)
        rw [if_neg (fun hh => h1 hh.symm)] at this
        exact this
      rw [e1, mul_zero]
    · have : (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K) 0 ^ d' 0 = 0 := zero_pow h0
      rw [this, zero_mul, map_zero, mul_zero]

theorem coeff_pow_mem {i : PowerSeries K} {n : ℕ} (hi : ∀ m < n, PowerSeries.coeff m i ∈ R)
    (k : ℕ) : ∀ m < n, PowerSeries.coeff m (i ^ k) ∈ R := by
  induction k with
  | zero =>
    intro m _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Subring.sum_mem _ fun p hp => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact R.mul_mem (ih _ (by omega)) (hi _ (by omega))

theorem intPS_of_law_eq_zero {F : MvPowerSeries (Fin 2) K} (hF : IntMv R F)
    (hF0 : ∀ d : Fin 2 →₀ ℕ, d 0 = 0 → MvPowerSeries.coeff d F =
      MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
    {i : PowerSeries K} (hi : PowerSeries.constantCoeff i = 0)
    (hz : MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) F = 0) :
    IntPS R i := by
  have ha : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) s) = 0 := by
    intro s
    fin_cases s
    · exact PowerSeries.constantCoeff_X
    · exact hi
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hi' : i = - MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K)
      (F - MvPowerSeries.X (1 : Fin 2)) := by
    rw [MvPowerSeries.subst_sub hs, hz, MvPowerSeries.subst_X hs, zero_sub, neg_neg]
    rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc : PowerSeries.coeff n i = - MvPowerSeries.coeff (Finsupp.single () n)
        (MvPowerSeries.subst (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K)
          (F - MvPowerSeries.X (1 : Fin 2))) := by
      conv_lhs => rw [hi']
      exact map_neg _ _
    rw [hc, coeff_substMv_two _ ha]
    refine R.neg_mem (finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_)
    by_cases h0 : d 0 = 0
    · rw [map_sub, hF0 d h0, sub_self, zero_mul]
      exact R.zero_mem
    · refine R.mul_mem ?_ ?_
      · rw [map_sub]
        exact R.sub_mem (hF d) (intMv_X 1 d)
      · have e1 : MvPowerSeries.coeff (Finsupp.single () n)
            ((![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) 0 ^ d 0 *
              (![PowerSeries.X, i] : Fin 2 → MvPowerSeries Unit K) 1 ^ d 1) =
            if d 0 ≤ n then PowerSeries.coeff (n - d 0) (i ^ d 1) else 0 :=
          PowerSeries.coeff_X_pow_mul' (i ^ d 1) (d 0) n
        rw [e1]
        split_ifs with hle
        · exact coeff_pow_mem ih (d 1) _ (by omega)
        · exact R.zero_mem

theorem endInt_neg_one (h : IsLogPair l linv) (hF : FGInt R l linv) : EndInt R l linv (-1) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  refine intPS_of_law_eq_zero hF (coeff_law_of_zero h) (constantCoeff_mulBy h (-1)) ?_
  rw [← fadd_eq_substMv h hX (constantCoeff_mulBy h (-1)), mulBy_eq_fmul]
  have := fadd_fmul_neg h 1 hX
  rwa [fmul_one h hX] at this

theorem endInt_neg (h : IsLogPair l linv) (hF : FGInt R l linv) {a : K}
    (ha : EndInt R l linv a) : EndInt R l linv (-a) := by
  rw [← neg_one_mul]
  exact endInt_mul h (endInt_neg_one h hF) ha

theorem isPt_flin (h : IsLogPair l linv) (hF : FGInt R l linv) {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ j, EndInt R l linv (c j)) {u : n → MvPowerSeries σ K}
    (hu : ∀ j, IsPt R (u j)) : IsPt R (flin l linv c u) := by
  classical
  have key : ∀ s : Finset n, IsPt R
      (PowerSeries.subst (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) linv) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1]
      exact ⟨map_zero _, fun _ => by rw [map_zero]; exact R.zero_mem⟩
    | insert j s hj ih =>
      have h0 : MvPowerSeries.constantCoeff
          (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun j _ => constantCoeff_C_mul_l h (c j) (hu j).1
      have := isPt_fadd h hF (isPt_fmul h (hc j) (hu j)) ih
      rw [fadd, l_fmul h (c j) (hu j).1, subst_l_linv h h0] at this
      rw [Finset.sum_insert hj]
      exact this
  exact key Finset.univ

end Integral

end Pts

open Pts in
theorem integralPointClosure' : PtClosure := by
  intro K _ R l linv h hF
  exact ⟨fun σ x y hx hy => isPt_fadd h hF hx hy, fun a ha σ x hx => isPt_fmul h ha hx,
    endInt_zero h, endInt_one h, endInt_neg_one h hF, fun a b ha hb => endInt_add h hF ha hb,
    fun a b ha hb => endInt_mul h ha hb⟩

end Formalism.L2.Th1.C
