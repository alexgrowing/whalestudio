import Formalism.PieriBlockIdeals.StatementLA
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.PieriBlockIdeals.PieriColumnMinors.PadicValIntProdElevenMultiples
import Formalism.PieriBlockIdeals.PieriColumnMinors.JointExactExponentStopHigh

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LA

open Formalism.GradedWeylDivisibility

theorem max_valuation_eq : MaxValEq := by
  intro l n
  rfl

theorem la_rowNu_antitone {r n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    Antitone (rowNu (r := r) ν) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold rowNu
  by_cases hb : b.val < n
  · have ha : a.val < n := by omega
    rw [dif_pos hb, dif_pos ha]
    exact hν (show (⟨a.val, ha⟩ : Fin n) ≤ ⟨b.val, hb⟩ from hab')
  · rw [dif_neg hb]
    exact Nat.zero_le _

theorem lambda_u_strict_anti : LamUStrictAnti := by
  unfold LamUStrictAnti
  intro r n ν hν a b hab
  have h1 := la_rowNu_antitone (r := r) ν hν (le_of_lt hab)
  have h2 : a.val < b.val := hab
  simp only [lamU]
  omega

theorem incl_z_monotone : InclZMono := by
  unfold InclZMono InclZ
  intro r n hn ν l e e' hee' hI
  obtain ⟨m, hm, h⟩ := hI
  refine ⟨m, hm, fun x hx => ?_⟩
  have e1 : m * l ^ e' = l ^ (e' - e) * (m * l ^ e) := by
    rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hee']
  rw [e1, Nat.cast_mul, mul_smul]
  exact Submodule.smul_mem _ _ (h x hx)

theorem la_posPairs_two : Formalism.RankGapBounds.JumpSetsAlt.posPairs 2 = {((0 : Fin 2), (1 : Fin 2))} := by
  decide

theorem exact_exponent_rank_two : ExactExponentRankTwo := by
  unfold ExactExponentRankTwo
  intro n ν l
  unfold Formalism.RankGapBounds.JumpSetsAlt.eExp
  rw [la_posPairs_two, Finset.sum_singleton]
  congr 1
  simp only [lamU, Fin.val_zero, Fin.val_one]
  omega

theorem joint_exact_z : JointExZ := by
  unfold JointExZ
  intro hA r n hn ν hν l hl
  exact Nat.sInf_le (hA r n hn ν hν l hl)

theorem la_strictAnti_gap {r : ℕ} (U : Fin r → ℤ) (hU : StrictAnti U) :
    ∀ (k : ℕ) (a b : Fin r), b.val = a.val + k → U b + k ≤ U a := by
  intro k
  induction k with
  | zero =>
    intro a b h
    have hab : b = a := Fin.ext (by omega)
    subst hab
    simp
  | succ k ih =>
    intro a b h
    have hb := b.isLt
    have hk : a.val + k < r := by omega
    have h1 := ih a ⟨a.val + k, hk⟩ rfl
    have h2 : U b < U ⟨a.val + k, hk⟩ :=
      hU (Fin.lt_iff_val_lt_val.mpr (by show a.val + k < b.val; omega))
    push_cast
    omega

theorem nu_of_specialization : NuOfSpec := by
  unfold NuOfSpec
  intro r U hU h0
  have hgap := la_strictAnti_gap U hU
  have hpos : ∀ a : Fin r, (r : ℤ) - 1 - a.val ≤ U a := by
    intro a
    have ha := a.isLt
    have hlast : a.val + (r - 1 - a.val) < r := by omega
    have h3 := hgap (r - 1 - a.val) a ⟨a.val + (r - 1 - a.val), hlast⟩ rfl
    have h4 := h0 ⟨a.val + (r - 1 - a.val), hlast⟩
    omega
  constructor
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    have hb := hpos b
    have ha := hpos a
    have key : U b + ((b.val - a.val : ℕ) : ℤ) ≤ U a := hgap (b.val - a.val) a b (by omega)
    simp only [nuOf]
    omega
  · funext a
    have ha := hpos a
    have hal := a.isLt
    simp only [lamU, rowNu, hal, ↓reduceDIte, nuOf, Fin.eta]
    omega

theorem joint_lemma_a_full : JointLemmaAFull := by
  intro ι D W hA hE l hl hexc τ
  obtain ⟨h1, h2⟩ := nu_of_specialization D.Nr (W.U τ) (W.anti τ) (fun a => (W.inRange τ a).1)
  have h3 := joint_exact_z hA D.Nr D.Nr le_rfl (nuOf (W.U τ)) h1 l hl
  rw [h2] at h3
  exact (hE l hl hexc τ).trans h3

theorem joint_lattice_inclusion : JointLatIncl := by
  unfold JointLatIncl
  intro hAR R _ _ r n hn ν hν l hl hu x
  rw [Submodule.mem_comap]
  simpa using hAR R r n hn ν hν l hl hu x x.2

theorem la_word_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (w : List (Fin r × Fin r × ℕ)) : applyWord R w (hw R hn ν) ∈ weyl R r n hn ν := Submodule.subset_span ⟨w, rfl⟩

theorem la_hw_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    hw R hn ν ∈ weyl R r n hn ν := la_word_mem R hn ν []

theorem la_incl_of_le {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) (hl : l.Prime)
    (h : dualWeyl ℤ r n ν ≤ weyl ℤ r n hn ν) : InclZ r n hn ν l e := by
  unfold InclZ
  exact ⟨1, hl.not_dvd_one, fun x hx => Submodule.smul_mem _ _ (h hx)⟩

theorem lattice_z_zero_columns : LatticeInclusionTrivialWeight := by
  unfold LatticeInclusionTrivialWeight
  intro r hn ν l hl
  apply la_incl_of_le hn ν _ _ hl
  intro x _
  have h1 : hw ℤ hn ν = 1 := by simp [hw]
  have hmem := la_hw_mem ℤ hn ν
  rw [h1] at hmem
  have hx : x = (coeff 0 x) • (1 : MvPolynomial (Fin r × Fin 0) ℤ) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
    exact MvPolynomial.eq_C_of_isEmpty x
  rw [hx]
  exact Submodule.smul_mem _ _ hmem

def la_xy (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (p q : ℕ) : MvPolynomial (Fin 2 × Fin n) R :=
  X ((0 : Fin 2), s) ^ p * X ((1 : Fin 2), s) ^ q

def la_monLat (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    Submodule R (MvPolynomial (Fin 2 × Fin n) R) :=
  Submodule.span R {f | ∃ p q, p + q = d ∧ f = la_xy R s p q}

def la_binLat (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    Submodule R (MvPolynomial (Fin 2 × Fin n) R) :=
  Submodule.span R {f | ∃ p q, p + q = d ∧
    f = ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q}

theorem la_mem_of_dvd (R : Type) [CommRing R] {n : ℕ} (s : Fin n) {d p q N : ℕ} (h : p + q = d)
    (hN : (p + q).choose q ∣ N) :
    (N : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q ∈ la_binLat R s d := by
  obtain ⟨c, rfl⟩ := hN
  have hmem : ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q ∈
      la_binLat R s d := Submodule.subset_span ⟨p, q, h, rfl⟩
  have h2 := Submodule.smul_mem _ (c : R) hmem
  rw [MvPolynomial.smul_eq_C_mul, map_natCast] at h2
  rw [Nat.cast_mul, mul_comm ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R), mul_assoc]
  exact h2

theorem la_coeff (A : Type) [CommRing A] (u v w : A) (p k : ℕ) :
    ((Polynomial.C u + Polynomial.X * Polynomial.C v) ^ p * Polynomial.C w).coeff k =
      (p.choose k : A) * (u ^ (p - k) * v ^ k * w) := by
  rw [Polynomial.coeff_mul_C]
  have h : (Polynomial.C u + Polynomial.X * Polynomial.C v) ^ p =
      ∑ m ∈ Finset.range (p + 1),
        Polynomial.C (v ^ m * u ^ (p - m) * (p.choose m : A)) * Polynomial.X ^ m := by
    rw [add_comm (Polynomial.C u), add_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [h, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · ring
  · rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem la_rowGen_X (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp only [rowGen, MvPolynomial.aeval_X]

theorem la_rowDiv_xy_zero (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (a : Fin 2) (p q k : ℕ) :
    rowDiv R a 0 k (la_xy R s p q) =
      (p.choose k : MvPolynomial (Fin 2 × Fin n) R) *
        (X ((0 : Fin 2), s) ^ (p - k) * X (a, s) ^ k * X ((1 : Fin 2), s) ^ q) := by
  have h0 : rowGen R a (0 : Fin 2) (X ((0 : Fin 2), s) : MvPolynomial (Fin 2 × Fin n) R) =
      Polynomial.C (X ((0 : Fin 2), s)) + Polynomial.X * Polynomial.C (X (a, s)) := by
    rw [la_rowGen_X, if_pos rfl]
  have h1 : rowGen R a (0 : Fin 2) (X ((1 : Fin 2), s) : MvPolynomial (Fin 2 × Fin n) R) =
      Polynomial.C (X ((1 : Fin 2), s)) := by
    rw [la_rowGen_X, if_neg (show ¬ ((1 : Fin 2) = 0) by decide), add_zero]
  simp only [rowDiv]
  rw [la_xy, map_mul, map_pow, map_pow, h0, h1, ← Polynomial.C_pow, la_coeff]

theorem la_rowDiv_xy_one (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (a : Fin 2) (p q k : ℕ) :
    rowDiv R a 1 k (la_xy R s p q) =
      (q.choose k : MvPolynomial (Fin 2 × Fin n) R) *
        (X ((1 : Fin 2), s) ^ (q - k) * X (a, s) ^ k * X ((0 : Fin 2), s) ^ p) := by
  have h0 : rowGen R a (1 : Fin 2) (X ((1 : Fin 2), s) : MvPolynomial (Fin 2 × Fin n) R) =
      Polynomial.C (X ((1 : Fin 2), s)) + Polynomial.X * Polynomial.C (X (a, s)) := by
    rw [la_rowGen_X, if_pos rfl]
  have h1 : rowGen R a (1 : Fin 2) (X ((0 : Fin 2), s) : MvPolynomial (Fin 2 × Fin n) R) =
      Polynomial.C (X ((0 : Fin 2), s)) := by
    rw [la_rowGen_X, if_neg (show ¬ ((0 : Fin 2) = 1) by decide), add_zero]
  simp only [rowDiv]
  rw [la_xy, map_mul, map_pow, map_pow, h0, h1, ← Polynomial.C_pow,
    mul_comm (Polynomial.C (X ((0 : Fin 2), s) ^ p)), la_coeff]

theorem la_rowDiv_nat (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k N : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k ((N : MvPolynomial (Fin r × Fin n) R) * f) =
      (N : MvPolynomial (Fin r × Fin n) R) * rowDiv R a b k f := by
  simp only [rowDiv, map_mul, map_natCast]
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul]

theorem choose_dvd_choose_mul_right (p k q : ℕ) :
    (p + (k + q)).choose (k + q) ∣ (p + k + q).choose q * (p + k).choose k := by
  have key := Nat.choose_mul (n := p + k + q) (k := k + q) (s := q) (by omega)
  rw [show p + k + q - q = p + k by omega, show k + q - q = k by omega] at key
  rw [show p + (k + q) = p + k + q by omega]
  exact ⟨(k + q).choose q, by linarith [key]⟩

theorem choose_dvd_choose_mul_left (p k q : ℕ) :
    (p + k + q).choose q ∣ (p + (q + k)).choose (q + k) * (q + k).choose k := by
  have key := Nat.choose_mul (n := p + k + q) (k := q + k) (s := q) (by omega)
  rw [show p + k + q - q = p + k by omega, show q + k - q = k by omega] at key
  have hs : (q + k).choose k = (q + k).choose q := (Nat.choose_symm_add).symm
  rw [show p + (q + k) = p + k + q by omega, hs]
  exact ⟨(p + k).choose k, by linarith [key]⟩

theorem fin_two_eq_zero_or_one : ∀ c : Fin 2, c = 0 ∨ c = 1 := by
  decide

theorem la_binLat_stable (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) (a b : Fin 2) (k : ℕ)
    (f : MvPolynomial (Fin 2 × Fin n) R) (hf : f ∈ la_binLat R s d) :
    rowDiv R a b k f ∈ la_binLat R s d := by
  rw [la_binLat] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    rw [la_rowDiv_nat]
    rcases fin_two_eq_zero_or_one b with rfl | rfl <;> rcases fin_two_eq_zero_or_one a with rfl | rfl
    · rw [la_rowDiv_xy_zero]
      by_cases hk : k ≤ p
      · have e : ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * (((p.choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((0 : Fin 2), s) ^ (p - k) * X ((0 : Fin 2), s) ^ k * X ((1 : Fin 2), s) ^ q)) =
            (p.choose k : R) • (((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q) := by
          rw [← pow_add, Nat.sub_add_cancel hk, MvPolynomial.smul_eq_C_mul, map_natCast, la_xy]
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, q, hpq, rfl⟩)
      · rw [Nat.choose_eq_zero_of_lt (show p < k by omega)]
        simp
    · rw [la_rowDiv_xy_zero]
      by_cases hk : k ≤ p
      · obtain ⟨p', rfl⟩ : ∃ p', p = p' + k := ⟨p - k, by omega⟩
        have e : ((p' + k + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * ((((p' + k).choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((0 : Fin 2), s) ^ (p' + k - k) * X ((1 : Fin 2), s) ^ k * X ((1 : Fin 2), s) ^ q)) =
            (((p' + k + q).choose q * (p' + k).choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
              la_xy R s p' (k + q) := by
          rw [Nat.add_sub_cancel, la_xy]
          push_cast
          ring
        rw [e]
        exact la_mem_of_dvd R s (by omega) (choose_dvd_choose_mul_right p' k q)
      · rw [Nat.choose_eq_zero_of_lt (show p < k by omega)]
        simp
    · rw [la_rowDiv_xy_one]
      by_cases hk : k ≤ q
      · obtain ⟨q', rfl⟩ : ∃ q', q = q' + k := ⟨q - k, by omega⟩
        have e : ((p + (q' + k)).choose (q' + k) : MvPolynomial (Fin 2 × Fin n) R) *
            ((((q' + k).choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((1 : Fin 2), s) ^ (q' + k - k) * X ((0 : Fin 2), s) ^ k * X ((0 : Fin 2), s) ^ p)) =
            (((p + (q' + k)).choose (q' + k) * (q' + k).choose k : ℕ) :
              MvPolynomial (Fin 2 × Fin n) R) * la_xy R s (p + k) q' := by
          rw [Nat.add_sub_cancel, la_xy]
          push_cast
          ring
        rw [e]
        exact la_mem_of_dvd R s (by omega) (choose_dvd_choose_mul_left p k q')
      · rw [Nat.choose_eq_zero_of_lt (show q < k by omega)]
        simp
    · rw [la_rowDiv_xy_one]
      by_cases hk : k ≤ q
      · have e : ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * (((q.choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((1 : Fin 2), s) ^ (q - k) * X ((1 : Fin 2), s) ^ k * X ((0 : Fin 2), s) ^ p)) =
            (q.choose k : R) • (((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q) := by
          rw [← pow_add, Nat.sub_add_cancel hk, MvPolynomial.smul_eq_C_mul, map_natCast, la_xy]
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, q, hpq, rfl⟩)
      · rw [Nat.choose_eq_zero_of_lt (show q < k by omega)]
        simp
  | zero =>
    rw [show rowDiv R a b k 0 = 0 from by simp [rowDiv]]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [show rowDiv R a b k (x + y) = rowDiv R a b k x + rowDiv R a b k y from by simp [rowDiv]]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [show rowDiv R a b k (c • x) = c • rowDiv R a b k x from by simp [rowDiv]]
    exact Submodule.smul_mem _ c hx

def la_mono {n : ℕ} (s : Fin n) (p q : ℕ) : Fin 2 × Fin n →₀ ℕ :=
  Finsupp.single ((0 : Fin 2), s) p + Finsupp.single ((1 : Fin 2), s) q

theorem la_xy_eq (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (p q : ℕ) :
    la_xy R s p q = monomial (la_mono s p q) 1 := by
  rw [la_xy, la_mono, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]

theorem la_mono_inj {n : ℕ} (s : Fin n) {p q p' q' : ℕ} (h : la_mono s p q = la_mono s p' q') :
    p = p' ∧ q = q' := by
  constructor
  · simpa [la_mono, Finsupp.single_apply] using congrArg (fun m => m ((0 : Fin 2), s)) h
  · simpa [la_mono, Finsupp.single_apply] using congrArg (fun m => m ((1 : Fin 2), s)) h

theorem la_coeff_binLat {n : ℕ} (s : Fin n) (d : ℕ) (f : MvPolynomial (Fin 2 × Fin n) ℤ)
    (hf : f ∈ la_binLat ℤ s d) (p q : ℕ) :
    ((p + q).choose q : ℤ) ∣ coeff (la_mono s p q) f := by
  rw [la_binLat] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p', q', hpq, rfl⟩ := hx
    rw [la_xy_eq, ← nsmul_eq_mul, coeff_smul, coeff_monomial]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := la_mono_inj s h
      simp
    · simp
  | zero => simp
  | add x y _ _ hx hy =>
    rw [coeff_add]
    exact dvd_add hx hy
  | smul a x _ hx =>
    rw [coeff_smul, smul_eq_mul]
    exact Dvd.dvd.mul_left hx a

theorem la_arith (l d : ℕ) (hl : l.Prime) :
    ∃ m : ℕ, ¬ l ∣ m ∧ ∀ i ≤ d, d.choose i ∣ m * l ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l d := by
  refine ⟨∏ i ∈ Finset.range (d + 1), d.choose i / l ^ ((d.choose i).factorization l), ?_, ?_⟩
  · rw [Prime.dvd_finset_prod_iff hl.prime]
    push_neg
    intro i hi
    exact Nat.not_dvd_ordCompl hl (Nat.choose_pos (by rw [Finset.mem_range] at hi; omega)).ne'
  · intro i hi
    have hmem : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    calc d.choose i = l ^ ((d.choose i).factorization l) *
          (d.choose i / l ^ ((d.choose i).factorization l)) :=
          (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
      _ ∣ l ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l d *
          ∏ j ∈ Finset.range (d + 1), d.choose j / l ^ ((d.choose j).factorization l) :=
        mul_dvd_mul (Nat.pow_dvd_pow l (Finset.le_sup (f := fun j => (d.choose j).factorization l) hmem))
          (Finset.dvd_prod_of_mem _ hmem)
      _ = _ := mul_comm _ _

theorem la_arith_conv (l d m e : ℕ) (hl : l.Prime) (hm : ¬ l ∣ m)
    (h : ∀ i ≤ d, d.choose i ∣ m * l ^ e) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l d ≤ e := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  refine Finset.sup_le (fun i hi => ?_)
  have hi' : i ≤ d := by rw [Finset.mem_range] at hi; omega
  have hc0 : d.choose i ≠ 0 := (Nat.choose_pos hi').ne'
  have hne : m * l ^ e ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hl.ne_zero)
  have h1 := Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hc0 hne).mpr (h i hi')) l
  have h2 : (m * l ^ e).factorization l = e := by
    rw [Nat.factorization_mul hm0 (pow_ne_zero _ hl.ne_zero)]
    simp [Nat.factorization_eq_zero_of_not_dvd hm, hl.factorization_self]
  rw [h2] at h1
  exact h1

theorem la_smul_monLat {n : ℕ} (s : Fin n) (d N : ℕ) (hN : ∀ i ≤ d, d.choose i ∣ N)
    (y : MvPolynomial (Fin 2 × Fin n) ℤ) (hy : y ∈ la_monLat ℤ s d) :
    ((N : ℕ) : ℤ) • y ∈ la_binLat ℤ s d := by
  rw [la_monLat] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact la_mem_of_dvd ℤ s hpq (by rw [hpq]; exact hN q (by omega))
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx

theorem la_core {n : ℕ} (s : Fin n) (d : ℕ) (g : MvPolynomial (Fin 2 × Fin n) ℤ) (hg : g ≠ 0)
    (l e : ℕ) (hl : l.Prime) :
    (∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ (la_monLat ℤ s d).map (LinearMap.mulLeft ℤ g),
      ((m * l ^ e : ℕ) : ℤ) • x ∈ (la_binLat ℤ s d).map (LinearMap.mulLeft ℤ g)) ↔
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l d ≤ e := by
  constructor
  · rintro ⟨m, hm, h⟩
    refine la_arith_conv l d m e hl hm (fun i hi => ?_)
    have hy : la_xy ℤ s (d - i) i ∈ la_monLat ℤ s d :=
      Submodule.subset_span ⟨d - i, i, by omega, rfl⟩
    obtain ⟨z, hz, hgz⟩ := Submodule.mem_map.mp (h _ (Submodule.mem_map_of_mem hy))
    simp only [LinearMap.mulLeft_apply] at hgz
    have hz' : z = ((m * l ^ e : ℕ) : ℤ) • la_xy ℤ s (d - i) i := by
      apply mul_left_cancel₀ hg
      rw [hgz, mul_smul_comm]
    have hc := la_coeff_binLat s d z hz (d - i) i
    rw [hz', la_xy_eq, coeff_smul, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one,
      show d - i + i = d by omega] at hc
    exact_mod_cast hc
  · intro he
    obtain ⟨m, hm, hdiv⟩ := la_arith l d hl
    refine ⟨m, hm, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨((m * l ^ e : ℕ) : ℤ) • y,
      la_smul_monLat s d (m * l ^ e)
        (fun i hi => (hdiv i hi).trans (Nat.mul_dvd_mul_left m (Nat.pow_dvd_pow l he))) y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    exact mul_smul_comm _ _ _

theorem la_lpMinor_one (R : Type) [CommRing R] {r n : ℕ} (s : ℕ) (hs : s = 1) (hr : s ≤ r)
    (hn : s ≤ n) :
    lpMinor R s hr hn = X ((⟨0, by omega⟩ : Fin r), (⟨0, by omega⟩ : Fin n)) := by
  subst hs
  show Matrix.det (Matrix.of fun p q : Fin 1 =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) = _
  rw [Matrix.det_fin_one]
  rfl

theorem highest_weight_one_column (R : Type) [CommRing R] {r : ℕ} (hn : 1 ≤ r) (ν : Fin 1 → ℕ) :
    hw R hn ν = X ((⟨0, hn⟩ : Fin r), (0 : Fin 1)) ^ ν 0 := by
  show ∏ s : Fin 1, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s) = _
  rw [Fin.prod_univ_one, show nuNext ν 0 = 0 from dif_neg (by decide), Nat.sub_zero]
  exact congrArg (· ^ ν 0) (la_lpMinor_one R _ rfl _ _)

theorem la_weyl_le_of_stable (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (L : Submodule R (MvPolynomial (Fin r × Fin n) R)) (h0 : hw R hn ν ∈ L)
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R), f ∈ L →
      rowDiv R a b k f ∈ L) : weyl R r n hn ν ≤ L := by
  show Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν)) ≤ L
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact hs x.1 x.2.1 x.2.2 _ ih

theorem la_weyl_r2n1 (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) :
    weyl R 2 1 hn ν = la_binLat R (0 : Fin 1) (ν 0) := by
  have hhw : hw R hn ν = la_xy R (0 : Fin 1) (ν 0) 0 := by
    rw [highest_weight_one_column, la_xy, pow_zero, mul_one]
    try rfl
  apply le_antisymm
  · refine la_weyl_le_of_stable R hn ν _ ?_ (fun a b k f hf => la_binLat_stable R 0 (ν 0) a b k f hf)
    rw [hhw, la_binLat]
    exact Submodule.subset_span ⟨ν 0, 0, by simp, by simp⟩
  · rw [la_binLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    have h := la_word_mem R hn ν [((1 : Fin 2), (0 : Fin 2), q)]
    have e : applyWord R [((1 : Fin 2), (0 : Fin 2), q)] (hw R hn ν) =
        ((p + q).choose q : MvPolynomial (Fin 2 × Fin 1) R) * la_xy R 0 p q := by
      show rowDiv R 1 0 q (hw R hn ν) = _
      rw [hhw, ← hpq, la_rowDiv_xy_zero]
      simp [la_xy]
    rw [e] at h
    exact h

theorem la_mono_of_weight {m : Fin 2 × Fin 1 →₀ ℕ} {ν : Fin 1 → ℕ}
    (h : Finsupp.weight (colW 2 1) m = ν) :
    m = la_mono (0 : Fin 1) (m (0, 0)) (m (1, 0)) ∧ m (0, 0) + m (1, 0) = ν 0 := by
  have h0 := congrFun h 0
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h0
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, colW] at h0
  refine ⟨?_, h0⟩
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [la_mono, Finsupp.single_apply]

theorem la_nabla_r2n1 (R : Type) [CommRing R] (ν : Fin 1 → ℕ) :
    dualWeyl R 2 1 ν = la_monLat R (0 : Fin 1) (ν 0) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ weightedHomogeneousSubmodule R (colW 2 1) ν := (Submodule.mem_inf.mp hx).1
    rw [mem_weightedHomogeneousSubmodule] at hx'
    rw [x.as_sum]
    refine Submodule.sum_mem _ (fun d hd => ?_)
    obtain ⟨hd', hsum⟩ := la_mono_of_weight (hx' (mem_support_iff.mp hd))
    have e : monomial d (coeff d x) = coeff d x • la_xy R (0 : Fin 1) (d (0, 0)) (d (1, 0)) := by
      rw [la_xy_eq, ← hd', smul_monomial, smul_eq_mul, mul_one]
    rw [e, la_monLat]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hsum, rfl⟩)
  · rw [la_monLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    show la_xy R (0 : Fin 1) p q ∈ weightedHomogeneousSubmodule R (colW 2 1) ν ⊓ _
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule, la_xy_eq]
      apply isWeightedHomogeneous_monomial
      funext j
      fin_cases j
      simp [la_mono, colW, Finsupp.weight_single, hpq]
    · simp only [Submodule.mem_iInf]
      intro a b hab
      exact ((ne_of_lt hab) (Subsingleton.elim a b)).elim

theorem la_binForm_apply (R : Type) [CommRing R] (d : ℕ) (c : Fin (d + 1) → R) :
    binForm R d c = ∑ i : Fin (d + 1), c i • la_xy R (0 : Fin 1) (d - i.val) i.val := by
  simp only [binForm, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, la_xy]

theorem la_binForm_single (R : Type) [CommRing R] (d : ℕ) (i : Fin (d + 1)) (t : R) :
    binForm R d (Pi.single i t) = t • la_xy R (0 : Fin 1) (d - i.val) i.val := by
  rw [la_binForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem la_coeff_binForm (R : Type) [CommRing R] (d : ℕ) (c : Fin (d + 1) → R) (i : Fin (d + 1)) :
    coeff (la_mono (0 : Fin 1) (d - i.val) i.val) (binForm R d c) = c i := by
  rw [la_binForm_apply, coeff_sum, Finset.sum_eq_single i]
  · rw [coeff_smul, la_xy_eq, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [coeff_smul, la_xy_eq, coeff_monomial, if_neg, smul_zero]
    intro h
    exact hj (Fin.ext (la_mono_inj 0 h).2)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem binary_form_injective : BinFormInj := by
  unfold BinFormInj
  intro R _ d c c' h
  funext i
  rw [← la_coeff_binForm R d c i, ← la_coeff_binForm R d c' i, h]

theorem la_range_binForm (R : Type) [CommRing R] (d : ℕ) :
    LinearMap.range (binForm R d) = la_monLat R (0 : Fin 1) d := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [la_binForm_apply, la_monLat]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨d - i.val, i.val, by have := i.isLt; omega, rfl⟩))
  · rw [la_monLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    refine ⟨Pi.single ⟨q, by omega⟩ 1, ?_⟩
    rw [la_binForm_single, one_smul]
    simp only [Fin.val_mk, show d - q = p by omega]

theorem nabla_rank_two_one_column : DualWeylBinaryForms := by
  unfold DualWeylBinaryForms
  intro R _ ν
  rw [la_nabla_r2n1, la_range_binForm]

theorem la_diagBinom_apply (R : Type) [CommRing R] (d : ℕ) (c : Fin (d + 1) → R) (i : Fin (d + 1)) :
    Formalism.CohomologicalDescent.diagBinom R d c i = (d.choose i.val : R) * c i := by
  simp [Formalism.CohomologicalDescent.diagBinom]

theorem delta_rank_two_one_column : WeylRankTwoOneColumnImage := by
  unfold WeylRankTwoOneColumnImage
  intro R _ hn ν
  rw [la_weyl_r2n1]
  apply le_antisymm
  · rw [la_binLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    have hsingle : Formalism.CohomologicalDescent.diagBinom R (ν 0) (Pi.single (⟨q, by omega⟩ : Fin (ν 0 + 1)) 1) =
        Pi.single ⟨q, by omega⟩ ((ν 0).choose q : R) := by
      funext j
      rw [la_diagBinom_apply]
      by_cases hj : j = ⟨q, by omega⟩
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    refine Submodule.mem_map.mpr ⟨Formalism.CohomologicalDescent.diagBinom R (ν 0) (Pi.single ⟨q, by omega⟩ 1),
      LinearMap.mem_range_self _ _, ?_⟩
    rw [hsingle, la_binForm_single, MvPolynomial.smul_eq_C_mul, map_natCast]
    simp only [Fin.val_mk, ← hpq, Nat.add_sub_cancel]
  · rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨c, rfl⟩
    rw [Submodule.mem_comap, la_binForm_apply, la_binLat]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hi := i.isLt
    have hg : ((ν 0).choose i.val : R) • la_xy R (0 : Fin 1) (ν 0 - i.val) i.val ∈
        Submodule.span R {f | ∃ p q, p + q = ν 0 ∧
          f = ((p + q).choose q : MvPolynomial (Fin 2 × Fin 1) R) * la_xy R 0 p q} := by
      rw [MvPolynomial.smul_eq_C_mul, map_natCast]
      exact Submodule.subset_span ⟨ν 0 - i.val, i.val, by omega,
        by rw [show ν 0 - i.val + i.val = ν 0 by omega]⟩
    rw [la_diagBinom_apply, mul_comm ((ν 0).choose i.val : R), mul_smul]
    exact Submodule.smul_mem _ _ hg

theorem la_eExp_r2n1 (ν : Fin 1 → ℕ) (l : ℕ) :
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l = Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) := by
  rw [exact_exponent_rank_two 1 ν l]
  have h0 : rowNu (r := 2) ν 0 = ν 0 := dif_pos (by decide)
  have h1 : rowNu (r := 2) ν 1 = 0 := dif_neg (by decide)
  rw [h0, h1, Nat.sub_zero]

theorem lemma_a_rank_two_one_column : LemmaAR_r2n1 := by
  unfold LemmaAR_r2n1
  intro R _ hn ν l hl hu x hx
  rw [la_nabla_r2n1] at hx
  rw [la_weyl_r2n1, la_eExp_r2n1]
  obtain ⟨m, hm, hdiv⟩ := la_arith l (ν 0) hl
  obtain ⟨u, hu'⟩ := hu m hm
  have key : ∀ y ∈ la_monLat R (0 : Fin 1) (ν 0),
      ((m : R) * (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0)) • y ∈ la_binLat R 0 (ν 0) := by
    intro y hy
    rw [la_monLat] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, hpq, rfl⟩ := hz
      have h := la_mem_of_dvd R (0 : Fin 1) hpq (N := m * l ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0))
        (by rw [hpq]; exact hdiv q (by omega))
      rw [MvPolynomial.smul_eq_C_mul, ← Nat.cast_pow, ← Nat.cast_mul, map_natCast]
      exact h
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [smul_comm]
      exact Submodule.smul_mem _ c ha
  have h2 := Submodule.smul_mem _ (↑u⁻¹ : R) (key x hx)
  rwa [smul_smul, ← mul_assoc, ← hu', Units.inv_mul, one_mul] at h2

theorem sharp_rank_two_one_column : SharpInclusionRankTwoOneColumn := by
  unfold SharpInclusionRankTwoOneColumn
  intro hn ν l e hl
  have hc := la_core (0 : Fin 1) (ν 0) 1 one_ne_zero l e hl
  simp only [LinearMap.mulLeft_one, Submodule.map_id] at hc
  unfold InclZ
  rw [la_nabla_r2n1, la_weyl_r2n1]
  exact hc

theorem lattice_z_rank_two_one_column : LemmaAZ_r2n1 := by
  unfold LemmaAZ_r2n1
  intro hn ν l hl
  rw [la_eExp_r2n1]
  exact (sharp_rank_two_one_column hn ν l _ hl).mpr le_rfl

theorem exact_z_rank_two_one_column : ExZR2N1 := by
  unfold ExZR2N1
  intro hn ν l hl
  rw [la_eExp_r2n1]
  unfold exZ
  have hset : {e : ℕ | InclZ 2 1 hn ν l e} = {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e} := by
    ext e
    exact sharp_rank_two_one_column hn ν l e hl
  rw [hset]
  have hmem : Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ∈ {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e} :=
    le_refl (Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0))
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ (fun b hb => hb))

theorem lattice_z_rank_one : LatticeInclusionRankOne := by
  unfold LatticeInclusionRankOne
  intro n hn ν hν l hl
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact lattice_z_zero_columns 1 hn ν l hl
  · apply la_incl_of_le hn ν _ _ hl
    intro x hx
    have hx' : x ∈ weightedHomogeneousSubmodule ℤ (colW 1 1) ν := (Submodule.mem_inf.mp hx).1
    rw [mem_weightedHomogeneousSubmodule] at hx'
    have hhw : hw ℤ hn ν = X ((0 : Fin 1), (0 : Fin 1)) ^ ν 0 := highest_weight_one_column ℤ hn ν
    rw [x.as_sum]
    refine Submodule.sum_mem _ (fun d hd => ?_)
    have hwd := hx' (mem_support_iff.mp hd)
    have hd0 : d = Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0) := by
      have h0 := congrFun hwd 0
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h0
      simp [Fintype.sum_prod_type, colW] at h0
      ext ⟨i, j⟩
      fin_cases i
      fin_cases j
      simpa using h0
    have e : monomial (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0))
        (coeff (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0)) x) =
        coeff (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) (ν 0)) x • hw ℤ hn ν := by
      rw [hhw, X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]
    rw [hd0, e]
    exact Submodule.smul_mem _ _ (la_hw_mem ℤ hn ν)

def la_det (R : Type) [CommRing R] : MvPolynomial (Fin 2 × Fin 2) R :=
  X ((0 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (1 : Fin 2)) -
    X ((0 : Fin 2), (1 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2))

theorem la_lpMinor_two (R : Type) [CommRing R] (s : ℕ) (hs : s = 2) (hr : s ≤ 2) (hn : s ≤ 2) :
    lpMinor R s hr hn = la_det R := by
  subst hs
  show Matrix.det (Matrix.of fun p q : Fin 2 =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin 2 × Fin 2) R)) = _
  rw [Matrix.det_fin_two]
  rfl

theorem highest_weight_rank_two (R : Type) [CommRing R] (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) :
    hw R hn ν = la_det R ^ ν 1 * la_xy R (0 : Fin 2) (ν 0 - ν 1) 0 := by
  show ∏ s : Fin 2, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s) = _
  rw [Fin.prod_univ_two, show nuNext ν 0 = ν 1 from dif_pos (by decide),
    show nuNext ν 1 = 0 from dif_neg (by decide), Nat.sub_zero]
  have e1 := la_lpMinor_one R (r := 2) (n := 2) ((0 : Fin 2).val + 1) (by decide) (by decide) (by decide)
  have e2 := la_lpMinor_two R ((1 : Fin 2).val + 1) (by decide) (by decide) (by decide)
  rw [e1, e2, la_xy, pow_zero, mul_one]
  exact mul_comm _ _

theorem la_rowGen_det_ne (R : Type) [CommRing R] (a b : Fin 2) (hab : a ≠ b) :
    rowGen R a b (la_det R) = Polynomial.C (la_det R) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl <;> rcases fin_two_eq_zero_or_one b with rfl | rfl
  · exact absurd rfl hab
  · simp [la_det, la_rowGen_X] <;> ring
  · simp [la_det, la_rowGen_X] <;> ring
  · exact absurd rfl hab

theorem la_rowGen_det_eq (R : Type) [CommRing R] (a : Fin 2) :
    rowGen R a a (la_det R) = Polynomial.C (la_det R) * (1 + Polynomial.X) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl
  · simp [la_det, la_rowGen_X] <;> ring
  · simp [la_det, la_rowGen_X] <;> ring

theorem la_rowDiv_tw_ne (R : Type) [CommRing R] (a b : Fin 2) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin 2 × Fin 2) R) :
    rowDiv R a b k (la_det R ^ c * f) = la_det R ^ c * rowDiv R a b k f := by
  simp only [rowDiv]
  rw [map_mul, map_pow, la_rowGen_det_ne R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]

theorem la_rowDiv_tw_eq (R : Type) [CommRing R] (a : Fin 2) (k c : ℕ)
    (f : MvPolynomial (Fin 2 × Fin 2) R) :
    rowDiv R a a k (la_det R ^ c * f) = la_det R ^ c *
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, (c.choose x.1 : MvPolynomial (Fin 2 × Fin 2) R) *
        rowDiv R a a x.2 f := by
  simp only [rowDiv]
  rw [map_mul, map_pow, la_rowGen_det_eq, mul_pow, ← Polynomial.C_pow, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  simp only [Polynomial.coeff_one_add_X_pow]

theorem la_tw_stable (R : Type) [CommRing R] (L : Submodule R (MvPolynomial (Fin 2 × Fin 2) R))
    (hs : ∀ (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) R), f ∈ L →
      rowDiv R a b k f ∈ L) (c : ℕ) (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) R)
    (hf : f ∈ L.map (LinearMap.mulLeft R (la_det R ^ c))) :
    rowDiv R a b k f ∈ L.map (LinearMap.mulLeft R (la_det R ^ c)) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  simp only [LinearMap.mulLeft_apply]
  by_cases hab : a = b
  · subst hab
    rw [la_rowDiv_tw_eq]
    refine Submodule.mem_map.mpr ⟨_, Submodule.sum_mem _ (fun x _ => ?_), rfl⟩
    rw [← nsmul_eq_mul]
    exact nsmul_mem (hs _ _ _ _ hg) _
  · rw [la_rowDiv_tw_ne R a b hab]
    exact Submodule.mem_map.mpr ⟨_, hs _ _ _ _ hg, rfl⟩

theorem la_xy_mem_binLat (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    la_xy R s d 0 ∈ la_binLat R s d := by
  rw [la_binLat]
  exact Submodule.subset_span ⟨d, 0, by simp, by simp⟩

theorem la_weyl_r2n2 (R : Type) [CommRing R] (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) :
    weyl R 2 2 hn ν =
      (la_binLat R (0 : Fin 2) (ν 0 - ν 1)).map (LinearMap.mulLeft R (la_det R ^ ν 1)) := by
  have hhw : hw R hn ν = la_det R ^ ν 1 * la_xy R (0 : Fin 2) (ν 0 - ν 1) 0 := highest_weight_rank_two R hn ν
  apply le_antisymm
  · refine la_weyl_le_of_stable R hn ν _ ?_ (fun a b k f hf => la_tw_stable R _
      (fun a b k f hf => la_binLat_stable R 0 (ν 0 - ν 1) a b k f hf) (ν 1) a b k f hf)
    rw [hhw]
    refine Submodule.mem_map.mpr ⟨la_xy R 0 (ν 0 - ν 1) 0, ?_, rfl⟩
    rw [la_binLat]
    exact Submodule.subset_span ⟨ν 0 - ν 1, 0, by simp, by simp⟩
  · rw [la_binLat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, ⟨p, q, hpq, rfl⟩, rfl⟩
    have h := la_word_mem R hn ν [((1 : Fin 2), (0 : Fin 2), q)]
    have e : applyWord R [((1 : Fin 2), (0 : Fin 2), q)] (hw R hn ν) =
        LinearMap.mulLeft R (la_det R ^ ν 1)
          (((p + q).choose q : MvPolynomial (Fin 2 × Fin 2) R) * la_xy R 0 p q) := by
      show rowDiv R 1 0 q (hw R hn ν) = _
      rw [hhw, la_rowDiv_tw_ne R 1 0 (by decide), ← hpq, la_rowDiv_xy_zero,
        LinearMap.mulLeft_apply]
      simp [la_xy]
    rw [e] at h
    exact h

theorem la_monLat_mul (R : Type) [CommRing R] {n : ℕ} (s : Fin n) {d d' : ℕ}
    {u u' : MvPolynomial (Fin 2 × Fin n) R} (hu : u ∈ la_monLat R s d)
    (hu' : u' ∈ la_monLat R s d') : u * u' ∈ la_monLat R s (d + d') := by
  have h := Submodule.mul_mem_mul hu hu'
  rw [la_monLat, la_monLat, Submodule.span_mul_span] at h
  rw [la_monLat]
  refine Submodule.span_mono ?_ h
  rintro f ⟨a, ⟨p, q, hpq, rfl⟩, b, ⟨p', q', hpq', rfl⟩, rfl⟩
  exact ⟨p + p', q + q', by omega, by simp only [la_xy]; ring⟩

def detPowMulMonomialSpan (c d : ℕ) : Submodule ℤ (MvPolynomial (Fin 2 × Fin 2) ℤ) :=
  (la_monLat ℤ (0 : Fin 2) d).map (LinearMap.mulLeft ℤ (la_det ℤ ^ c))

theorem la_T_mul {c d c' d' : ℕ} {f f' : MvPolynomial (Fin 2 × Fin 2) ℤ} (hf : f ∈ detPowMulMonomialSpan c d)
    (hf' : f' ∈ detPowMulMonomialSpan c' d') : f * f' ∈ detPowMulMonomialSpan (c + c') (d + d') := by
  rw [detPowMulMonomialSpan] at hf hf' ⊢
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hf
  obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hf'
  refine Submodule.mem_map.mpr ⟨u * u', la_monLat_mul ℤ (0 : Fin 2) hu hu', ?_⟩
  simp only [LinearMap.mulLeft_apply]
  ring

theorem la_T_xy (c p q : ℕ) : la_det ℤ ^ c * la_xy ℤ (0 : Fin 2) p q ∈ detPowMulMonomialSpan c (p + q) := by
  rw [detPowMulMonomialSpan]
  exact Submodule.mem_map.mpr ⟨la_xy ℤ (0 : Fin 2) p q, Submodule.subset_span ⟨p, q, rfl, rfl⟩, rfl⟩

theorem initial_minor_mem_det_span (s : ℕ) (I : Fin s → Fin 2) (hs : s ≤ 2) :
    initMinor ℤ I hs ∈ detPowMulMonomialSpan (if s = 2 then 1 else 0) (if s = 1 then 1 else 0) := by
  obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  · have h : initMinor ℤ I hs = 1 := Matrix.det_isEmpty
    rw [h]
    simpa [la_xy] using la_T_xy 0 0 0
  · have h : initMinor ℤ I hs = X (I 0, 0) := Matrix.det_fin_one _
    rw [h]
    rcases fin_two_eq_zero_or_one (I 0) with h0 | h0 <;> rw [h0]
    · simpa [la_xy] using la_T_xy 0 1 0
    · simpa [la_xy] using la_T_xy 0 0 1
  · have h : initMinor ℤ I hs = X (I 0, 0) * X (I 1, 1) - X (I 0, 1) * X (I 1, 0) :=
      Matrix.det_fin_two _
    have h2 := la_T_xy 1 0 0
    simp only [la_xy, pow_zero, pow_one, mul_one, add_zero] at h2
    show initMinor ℤ I hs ∈ detPowMulMonomialSpan 1 0
    rw [h]
    rcases fin_two_eq_zero_or_one (I 0) with h0 | h0 <;> rcases fin_two_eq_zero_or_one (I 1) with h1 | h1 <;> rw [h0, h1]
    · have e : X ((0 : Fin 2), (0 : Fin 2)) * X ((0 : Fin 2), (1 : Fin 2)) -
          X ((0 : Fin 2), (1 : Fin 2)) * X ((0 : Fin 2), (0 : Fin 2)) =
          (0 : MvPolynomial (Fin 2 × Fin 2) ℤ) := by ring
      rw [e]
      exact Submodule.zero_mem _
    · exact h2
    · have e : X ((1 : Fin 2), (0 : Fin 2)) * X ((0 : Fin 2), (1 : Fin 2)) -
          X ((1 : Fin 2), (1 : Fin 2)) * X ((0 : Fin 2), (0 : Fin 2)) = -la_det ℤ := by
        simp only [la_det]
        ring
      rw [e]
      exact Submodule.neg_mem _ h2
    · have e : X ((1 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (1 : Fin 2)) -
          X ((1 : Fin 2), (1 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2)) =
          (0 : MvPolynomial (Fin 2 × Fin 2) ℤ) := by ring
      rw [e]
      exact Submodule.zero_mem _

theorem prod_initial_minors_mem_det_span {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ 2) (I : ∀ k, Fin (sz k) → Fin 2)
    (S : Finset (Fin K)) :
    ∏ k ∈ S, initMinor ℤ (I k) (hsz k) ∈
      detPowMulMonomialSpan (∑ k ∈ S, if sz k = 2 then 1 else 0) (∑ k ∈ S, if sz k = 1 then 1 else 0) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    simpa [la_xy] using la_T_xy 0 0 0
  | @insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    exact la_T_mul (initial_minor_mem_det_span (sz k) (I k) (hsz k)) ih

theorem la_det_ne : la_det ℤ ≠ 0 := by
  intro h
  have h1 := congrArg
    (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => if v.1 = v.2 then (1 : ℤ) else 0)) h
  simp [la_det] at h1

theorem la_nabla_r2n2 (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) (hν : Antitone ν) :
    dualWeyl ℤ 2 2 ν = detPowMulMonomialSpan (ν 1) (ν 0 - ν 1) := by
  apply le_antisymm
  · rw [standardMonomialSpan 2 2 ν hν]
    apply Submodule.span_le.2
    rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
    have h1 := prod_initial_minors_mem_det_span sz hsz I Finset.univ
    have c1 : (∑ k : Fin K, if sz k = 2 then 1 else 0) = ν 1 := by
      rw [← hshape]
      unfold shapeDeg
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k _
      have := hsz k
      have e : ((1 : Fin 2).val < sz k) ↔ sz k = 2 := by
        simp only [Fin.val_one]
        omega
      simp only [e]
    have c0 : (∑ k : Fin K, if sz k = 1 then 1 else 0) + (∑ k : Fin K, if sz k = 2 then 1 else 0)
        = ν 0 := by
      rw [← hshape]
      unfold shapeDeg
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have := hsz k
      simp only [Fin.val_zero]
      split_ifs <;> omega
    have c2 : (∑ k : Fin K, if sz k = 1 then 1 else 0) = ν 0 - ν 1 := by omega
    rw [c1, c2] at h1
    exact h1
  · unfold detPowMulMonomialSpan
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.2
    rintro _ ⟨p, q, h, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    apply dualWeylSat ℤ 2 2 ν (((p + q).choose q : ℕ) : ℤ) _
      (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
    apply weylLeDual ℤ 2 2 hn ν hν
    rw [la_weyl_r2n2]
    refine ⟨_, Submodule.subset_span ⟨p, q, h, rfl⟩, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [MvPolynomial.smul_eq_C_mul, map_natCast]
    ring

theorem la_eExp_r2n2 (ν : Fin 2 → ℕ) (l : ℕ) :
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l = Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) := by
  rw [exact_exponent_rank_two 2 ν l]
  have h0 : rowNu (r := 2) ν 0 = ν 0 := dif_pos (by decide)
  have h1 : rowNu (r := 2) ν 1 = ν 1 := dif_pos (by decide)
  rw [h0, h1]

theorem sharp_rank_two_two_columns : SharpInclusionRankTwoTwoColumns := by
  unfold SharpInclusionRankTwoTwoColumns
  intro hn ν hν l e hl
  have hc := la_core (0 : Fin 2) (ν 0 - ν 1) (la_det ℤ ^ ν 1) (pow_ne_zero _ la_det_ne) l e hl
  unfold InclZ
  rw [la_nabla_r2n2 hn ν hν, la_weyl_r2n2 ℤ hn ν]
  exact hc

theorem lattice_z_rank_two_two_columns : LemmaAZ_r2n2 := by
  unfold LemmaAZ_r2n2
  intro hn ν hν l hl
  rw [la_eExp_r2n2]
  exact (sharp_rank_two_two_columns hn ν hν l _ hl).mpr le_rfl

theorem exact_z_rank_two_two_columns : ExZR2N2 := by
  unfold ExZR2N2
  intro hn ν hν l hl
  rw [la_eExp_r2n2]
  unfold exZ
  have hset : {e : ℕ | InclZ 2 2 hn ν l e} = {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e} := by
    ext e
    exact sharp_rank_two_two_columns hn ν hν l e hl
  rw [hset]
  have hmem : Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ∈
      {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e} :=
    le_refl (Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1))
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ (fun b hb => hb))

theorem lattice_z_rank_le_two : LatticeInclusionRankLeTwo := by
  unfold LatticeInclusionRankLeTwo
  intro r n hn hr ν hν l hl
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · exact lattice_z_zero_columns r hn ν l hl
  · obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
    · exact lattice_z_rank_one 1 hn ν hν l hl
    · exact lattice_z_rank_two_one_column hn ν l hl
  · obtain rfl : r = 2 := by omega
    exact lattice_z_rank_two_two_columns hn ν hν l hl

theorem la_dualWeyl_fg (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by
  have h : dualWeyl ℤ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℤ (∑ s, ν s) := by
    intro f hf
    have h1 := (mem_dualWeyl_iff.1 hf).1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← lclosedeq_weight_sum, h1 hm]
  exact Submodule.FG.of_le (homogeneousSubmodule_fg _ _ _) h

theorem la_uniform (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((N : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν := by
  classical
  obtain ⟨S, hS⟩ := la_dualWeyl_fg r n ν
  have hc := weylRational r n hn ν hν
  choose! c hc0 hc1 using hc
  have hSm : ∀ g ∈ S, g ∈ dualWeyl ℤ r n ν := fun g hg => hS ▸ Submodule.subset_span hg
  refine ⟨(∏ g ∈ S, c g).natAbs, ?_, ?_⟩
  · rw [Int.natAbs_ne_zero, Finset.prod_ne_zero_iff]
    exact fun g hg => hc0 g (hSm g hg)
  · intro x hx
    have key : (∏ g ∈ S, c g) • x ∈ weyl ℤ r n hn ν := by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem c hg
        rw [ht, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (hc1 g (hSm g hg))
      | zero => simp
      | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    rcases Int.natAbs_eq (∏ g ∈ S, c g) with h | h
    · rw [← h]
      exact key
    · have h2 : (((∏ g ∈ S, c g).natAbs : ℕ) : ℤ) = -(∏ g ∈ S, c g) := by omega
      rw [h2, neg_smul]
      exact Submodule.neg_mem _ key

theorem exact_z_specialization : ExZSpec := by
  unfold ExZSpec
  intro r n hn ν hν l hl
  obtain ⟨N, hN0, hN⟩ := la_uniform r n hn ν hν
  obtain ⟨v, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l hl.ne_one
  have hv : InclZ r n hn ν l v := by
    unfold InclZ
    refine ⟨m, hm, fun x hx => ?_⟩
    rw [mul_comm m, ← hNe]
    exact hN x hx
  exact Nat.sInf_mem (s := {e : ℕ | InclZ r n hn ν l e}) ⟨v, hv⟩

private theorem la_rowGen_map_lemma (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (g : MvPolynomial (Fin r × Fin n) ℤ) :
    rowGen R a b (map (Int.castRingHom R) g) =
      Polynomial.map (map (Int.castRingHom R)) (rowGen ℤ a b g) := by
  induction g using MvPolynomial.induction_on
  next z => simp [rowGen]
  next p q hp hq => rw [map_add, map_add, hp, hq, map_add, Polynomial.map_add]
  next p v hp =>
    simp only [map_mul, MvPolynomial.map_X, hp, Polynomial.map_mul, la_rowGen_X]
    congr 1
    split_ifs <;> simp

private theorem la_rowDiv_map_lemma_2 (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) ℤ) :
    rowDiv R a b k (map (Int.castRingHom R) g) = map (Int.castRingHom R) (rowDiv ℤ a b k g) := by
  simp only [rowDiv, la_rowGen_map_lemma, Polynomial.coeff_map]

private theorem la_applyWord_map_lemma_3 (R : Type) [CommRing R] {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ) :
    applyWord R w (map (Int.castRingHom R) g) = map (Int.castRingHom R) (applyWord ℤ w g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (map (Int.castRingHom R) g)) =
      map (Int.castRingHom R) (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g))
    rw [ih, la_rowDiv_map_lemma_2]

private theorem la_hw_map_lemma_4 (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom R) (hw ℤ hn ν) = hw R hn ν := by
  simp only [hw, lpMinor, map_prod, map_pow, RingHom.map_det, RingHom.mapMatrix_apply]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  congr 2
  ext p q
  simp

theorem la_map_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    map (Int.castRingHom R) f ∈ weyl R r n hn ν := by
  have hf' : f ∈ Submodule.span ℤ
      (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord ℤ w (hw ℤ hn ν)) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← la_applyWord_map_lemma_3, la_hw_map_lemma_4]
    exact la_word_mem R hn ν w
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    rw [map_zsmul]
    exact zsmul_mem hx z

theorem la_incl_R_of_Z (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (l e : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) (hZ : InclZ r n hn ν l e)
    (x : MvPolynomial (Fin r × Fin n) R) (hx : x ∈ dualWeyl R r n ν) :
    (l : R) ^ e • x ∈ weyl R r n hn ν := by
  obtain ⟨m, hm, h⟩ := hZ
  rw [standardMonomialSpanDomain R r n ν] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    have h1 : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := hshape ▸ bidetMem ℤ r n K sz hsz I
    have h2 := la_map_weyl R hn ν _ (h _ h1)
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, ldlat_map_bidet, ← MvPolynomial.smul_eq_C_mul]
      at h2
    obtain ⟨u, hu'⟩ := hu m hm
    have h3 := Submodule.smul_mem _ (↑u⁻¹ : R) h2
    rw [smul_smul] at h3
    convert h3 using 2
    simp only [eq_intCast]
    push_cast
    rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem lemma_a_real_of_integral : LemmaAROfZ := by
  unfold LemmaAROfZ LemmaAR
  intro hZ R _ _ r n hn ν hν l hl hu x hx
  exact la_incl_R_of_Z R r n hn ν l _ hu (hZ r n hn ν hν l hl) x hx

theorem la_map_smul (R : Type) [CommRing R] {σ : Type} (z : ℤ) (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom R) (z • f) = (z : R) • map (Int.castRingHom R) f := by
  rw [map_zsmul]
  exact (Int.cast_smul_eq_zsmul R z _).symm

theorem la_clear (R : Type) [CommRing R] (l : ℕ) (hl : l.Prime)
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z)
    {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ weyl R r n hn ν) :
    ∃ m : ℕ, ¬ l ∣ m ∧ ∃ f0 ∈ weyl ℤ r n hn ν, (m : R) • f = map (Int.castRingHom R) f0 := by
  have hf' : f ∈ Submodule.span R
      (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν)) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, hl.not_dvd_one, applyWord ℤ w (hw ℤ hn ν), la_word_mem ℤ hn ν w, ?_⟩
    rw [← la_applyWord_map_lemma_3, la_hw_map_lemma_4, Nat.cast_one, one_smul]
  | zero =>
    exact ⟨1, hl.not_dvd_one, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, hm1, f1, hf1, e1⟩ := hx
    obtain ⟨m2, hm2, f2, hf2, e2⟩ := hy
    refine ⟨m1 * m2, fun h => ((Nat.Prime.dvd_mul hl).mp h).elim hm1 hm2,
      (m2 : ℤ) • f1 + (m1 : ℤ) • f2,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hf1) (Submodule.smul_mem _ _ hf2), ?_⟩
    rw [map_add, map_zsmul, map_zsmul, ← e1, ← e2, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul, smul_add, Nat.cast_mul, Int.cast_natCast,
      Int.cast_natCast, mul_comm (m2 : R) (m1 : R)]
  | smul a x _ hx =>
    obtain ⟨m1, hm1, f1, hf1, e1⟩ := hx
    obtain ⟨m, hm, z, hz⟩ := hd a
    refine ⟨m * m1, fun h => ((Nat.Prime.dvd_mul hl).mp h).elim hm hm1, z • f1,
      Submodule.smul_mem _ _ hf1, ?_⟩
    rw [map_zsmul, ← e1, ← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul, ← hz, Nat.cast_mul]
    congr 1
    ring

theorem la_incl_of_gens (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) (hl : l.Prime)
    (h : ∀ g ∈ dualWeyl ℤ r n ν, ∃ m : ℕ, ¬ l ∣ m ∧
      ((m * l ^ e : ℕ) : ℤ) • g ∈ weyl ℤ r n hn ν) : InclZ r n hn ν l e := by
  obtain ⟨S, hS⟩ := la_dualWeyl_fg r n ν
  choose! M hM hMw using h
  have hS' : ∀ g ∈ S, g ∈ dualWeyl ℤ r n ν := by
    intro g hg
    rw [← hS]
    exact Submodule.subset_span hg
  unfold InclZ
  refine ⟨∏ g ∈ S, M g, ?_, fun x hx => ?_⟩
  · rw [Prime.dvd_finset_prod_iff hl.prime]
    push_neg
    exact fun g hg => hM g (hS' g hg)
  · rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨K, hK⟩ := Finset.dvd_prod_of_mem M hg
      rw [hK, show M g * K * l ^ e = K * (M g * l ^ e) by ring, Nat.cast_mul, mul_smul]
      exact Submodule.smul_mem _ _ (hMw g (hS' g hg))
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx

theorem incl_z_iff_incl_r : InclZIffR := by
  intro R _ _ _ l hl hu hd r n hn ν e
  constructor
  · intro hZ x hx
    exact la_incl_R_of_Z R r n hn ν l e hu hZ x hx
  · intro hR
    apply la_incl_of_gens r n hn ν l e hl
    intro g hg
    have h1 := hR _ (dualWeylMap ℤ R (Int.castRingHom R) r n ν g hg)
    obtain ⟨m, hm, f0, hf0, h2⟩ := la_clear R l hl hd hn ν _ h1
    refine ⟨m, hm, ?_⟩
    have h3 : map (Int.castRingHom R) (((m * l ^ e : ℕ) : ℤ) • g) = map (Int.castRingHom R) f0 := by
      rw [la_map_smul, ← h2, smul_smul]
      push_cast
      rfl
    have hinj : Function.Injective (map (Int.castRingHom R) :
        MvPolynomial (Fin r × Fin n) ℤ → MvPolynomial (Fin r × Fin n) R) :=
      map_injective _ (RingHom.injective_int (Int.castRingHom R))
    rw [hinj h3]
    exact hf0

theorem lemma_a_integral_of_real : LemmaAZOfR := by
  intro hR r n hn ν hν l hl
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.1 hl)
  let R := Localization.AtPrime (Ideal.span {(l : ℤ)})
  have hinj : Function.Injective (algebraMap ℤ R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(l : ℤ)}))
  have : CharZero R := charZero_of_injective_algebraMap hinj
  have hmem : ∀ t : ℤ, t ∈ (Ideal.span {(l : ℤ)}).primeCompl ↔ ¬ (l : ℤ) ∣ t := by
    intro t
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
  have hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R) := by
    intro m hm
    have h1 : (m : ℤ) ∈ (Ideal.span {(l : ℤ)}).primeCompl :=
      (hmem _).2 (by exact_mod_cast hm)
    have h2 := IsLocalization.map_units R (⟨(m : ℤ), h1⟩ : (Ideal.span {(l : ℤ)}).primeCompl)
    simpa using h2
  have hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z := by
    intro a
    obtain ⟨⟨z, t⟩, h1⟩ := IsLocalization.surj (Ideal.span {(l : ℤ)}).primeCompl a
    have ht := (hmem _).1 t.2
    simp only [eq_intCast] at h1
    refine ⟨(t : ℤ).natAbs, fun h => ht (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq (t : ℤ) with h | h
    · refine ⟨z, ?_⟩
      rw [← h1, mul_comm]
      congr 1
      rw [← Int.cast_natCast, ← h]
    · refine ⟨-z, ?_⟩
      have h2 : (((t : ℤ).natAbs : ℤ) : R) = -((t : ℤ) : R) := by
        rw [← Int.cast_neg]
        congr 1
        omega
      have h3 : (((t : ℤ).natAbs : ℕ) : R) = -((t : ℤ) : R) := by
        rw [← Int.cast_natCast]
        exact h2
      rw [h3, Int.cast_neg, ← h1]
      ring
  exact (incl_z_iff_incl_r R l hl hu hd r n hn ν _).2 (hR R r n hn ν hν l hl hu)

theorem la_exZ_le_of_U (hA : LemmaAZ) (r : ℕ) (U : Fin r → ℤ) (hU : StrictAnti U) (h0 : ∀ a, 0 ≤ U a)
    (l : ℕ) (hl : l.Prime) : exZ r r le_rfl (nuOf U) l ≤ Formalism.RankGapBounds.JumpSetsAlt.eExp U l := by
  obtain ⟨hanti, hlam⟩ := nu_of_specialization r U hU h0
  have h := joint_exact_z hA r r le_rfl (nuOf U) hanti l hl
  rwa [hlam] at h

theorem joint_lemma_a_inputs : JointLemmaAInputs := by
  intro ι D W hA hE hP l hl hexc
  refine ⟨joint_lemma_a_full ι D W hA hE l hl hexc, fun τ hτ => ⟨?_, ?_⟩⟩
  · exact (hP l hl hexc τ hτ).1.trans (la_exZ_le_of_U hA D.k (W.cloud τ)
      (Formalism.CohomologicalDescent.Joint.cloud_anti W τ) (fun a => (W.inRange τ _).1) l hl)
  · exact (hP l hl hexc τ hτ).2.trans (la_exZ_le_of_U hA (D.Nr - D.k) (W.rest τ)
      (Formalism.CohomologicalDescent.Joint.rest_anti W τ) (fun a => (W.inRange τ _).1) l hl)

end Formalism.CohomologicalDescent.LA
