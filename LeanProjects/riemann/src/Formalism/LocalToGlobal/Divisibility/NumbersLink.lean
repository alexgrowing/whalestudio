import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.QuotientMetricDivisors.FinalW

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions
open Formalism.LatticeIndexTer (ph)

namespace NumDatum

variable (N : NumDatum)

def topsPl : Finset (RPl N.R) :=
  N.TT.map ⟨fun t => (false, t), fun _ _ h => (Prod.ext_iff.1 h).2⟩

theorem mem_topsPl (ρ : RPl N.R) : ρ ∈ N.topsPl ↔ ρ.1 = false ∧ ρ.2 ∈ N.TT := by
  constructor
  · intro h
    rw [topsPl, Finset.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨rfl, ht⟩
  · rintro ⟨h1, h2⟩
    rw [topsPl, Finset.mem_map]
    exact ⟨ρ.2, h2, Prod.ext h1.symm rfl⟩

def aTPl (ρ : RPl N.R) : ℝ := ((N.aT ρ.2 : ℚ) : ℝ)

def nuPad (δ : Code N) (j : ℕ) (ρ : RPl N.R) (i : Fin N.Nm) : ℝ :=
  if i.1 < N.R.N (j - 1) then ((N.nu δ j ρ i.1 : ℚ) : ℝ) else 0

def eEN (δ : Code N) (j : ℕ) (ρ : RPl N.R) : ℝ :=
  (∑ i, ph (N.nuPad δ j ρ i)) - N.logHook j ρ - (if ρ ∈ N.topsPl then ph (N.aTPl ρ) else 0)

def dN (δ : Code N) (j : ℕ) (ρ : RPl N.R) : ℝ :=
  (∑ i, N.nuPad δ j ρ i) - (if ρ ∈ N.topsPl then N.aTPl ρ else 0) - (N.R.k : ℝ) * N.w j ρ

def sN (j : ℕ) : ℕ := N.R.k / 2 + (2 * j - 1) * ((N.R.t + 1) / 2)

structure NumFacts (δ : Code N) (Nc lam0 C0 ce Ch Sw C1 : ℝ) : Prop where
  logrd : Real.log N.rd ≤ N.sc.L
  logx : Real.log N.sc.x ≤ N.sc.L
  Nc0 : 0 ≤ Nc
  w2b : ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ z, N.w j z ≤ 2 * N.sc.b
  Om : |N.logOm| ≤ N.La
  lam : (N.R.m : ℝ) * lam0 ≤ N.sc.b
  lam0 : 0 ≤ lam0
  n2 : (N.Nm : ℝ) ^ 2 ≤ N.sc.b
  n3 : (N.R.m : ℝ) ^ 3 * (N.Nm : ℝ) ^ 2 * N.sc.L ≤ N.sc.b
  eta : (N.R.m : ℝ) * N.eta * (N.Nm : ℝ) * N.sc.L ≤ N.sc.b
  kN : (N.R.k : ℝ) * (N.Nm : ℝ) ≤ N.sc.b
  kS : (N.R.k : ℝ) * N.Sc ≤ N.sc.w'' N.R.n
  blkW : (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta ≤ N.sc.w'' N.R.n
  Nw : (N.Nm : ℝ) * N.sc.w'' N.R.n ≤ N.sc.b
  bN : N.sc.b' * (N.Nm : ℝ) ≤ N.sc.a
  mkb : (N.R.m : ℝ) * (N.R.k : ℝ) * N.sc.b' ≤ N.sc.a
  c1 : 1 ≤ C0
  c2 : C0 ≤ ce
  c3 : 0 ≤ Ch
  c4 : Ch ≤ C0
  c5 : Ch * N.Lp ≤ C0 * N.La
  C1two : 2 ≤ C1
  constant_weight_sum_bound : 2 * Sw ≤ C1 * N.Sc
  constant_succ_le : C1 + 1 ≤ C0
  sw : ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ z,
    ((N.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((N.R.t : ℝ) + 1)) / 2 ≤ N.w j z
  rowsA : ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ z, N.w j z + Sw ≤ N.sc.a * N.rd
  topsA : ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ t ∈ N.TT, ((N.aT t : ℚ) : ℝ) + N.w j (false, t) ≤ N.sc.a * N.rd
  nu0 : ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ z, ∀ i < N.R.N (j - 1), 0 ≤ N.nu δ j z i
  blk : ∀ j, 1 ≤ j → j ≤ N.R.m → ∀ z,
    (∑ i ∈ Finset.Ico N.R.k (N.R.N (j - 1)), ((N.nu δ j z i : ℚ) : ℝ)) ≤ (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta
  inter : ∀ z (i : ℕ) (h : i + 1 < N.R.k),
    N.sigPar z i < N.uW δ z ⟨i, by omega⟩ ∧ N.uW δ z ⟨i + 1, h⟩ < N.sigPar z i
  off : ∀ z, ¬ (z.1 = false ∧ z.2 ∈ N.TT) →
    0 ≤ (N.hc z).u ⟨N.R.k - 1, by have := N.R.m_add_three_le_k; omega⟩ + ((N.R.k : ℚ) - 1) / 2 ∧
    (((N.hc z).u ⟨0, by have := N.R.m_add_three_le_k; omega⟩ - ((N.R.k : ℚ) - 1) / 2 : ℚ) : ℝ) ≤ Sw
  top : ∀ t ∈ N.TT, 0 ≤ N.aT t ∧ 0 ≤ N.bT t ∧
    0 ≤ N.sigPar (false, t) (N.R.k - 2) + ((N.R.k : ℚ) - 2) / 2 ∧
    ((N.sigPar (false, t) 0 - ((N.R.k : ℚ) - 2) / 2 : ℚ) : ℝ) ≤ Sw

end NumDatum

namespace NumDatum

variable (N : NumDatum)

theorem univ_map_fin {α : Type} (n : ℕ) (f : ℕ → α) :
    Finset.univ.val.map (fun i : Fin n => f i.1) = (Multiset.range n).map f := by
  first
  | (rw [Fin.univ_val_map]
     show ((List.ofFn fun i : Fin n => f i.1 : List α) : Multiset α) = (((List.range n).map f : List α) : Multiset α)
     congr 1
     apply List.ext_getElem <;> simp)
  | (induction n with
     | zero => rfl
     | succ n ih => simp [Fin.univ_val_map, List.ofFn_succ', Multiset.range_succ])

theorem sum_pad (g : ℕ → ℝ) {n M : ℕ} (h : n ≤ M) :
    ∑ i : Fin M, (if i.1 < n then g i.1 else 0) = ∑ i ∈ Finset.range n, g i := by
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < n then g i else 0) M).trans ?_
  show ∑ i ∈ Finset.range M, (if i < n then g i else 0) = _
  rw [← Finset.sum_range_add_sum_Ico _ h]
  have h1 : ∑ i ∈ Finset.Ico n M, (if i < n then g i else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_Ico] at hi; omega))
  rw [h1, add_zero]
  exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))

theorem sum_lifts (F : ℕ → ℝ) {J : Type} [Fintype J] (eJ : J ≃ Fin N.R.m) :
    ∑ j : J, F ((eJ j).1 + 1) = ∑ l ∈ N.lifts, F l := by
  refine (Equiv.sum_comp eJ (fun i : Fin N.R.m => F (i.1 + 1))).trans ?_
  refine (Fin.sum_univ_eq_sum_range (fun i => F (i + 1)) N.R.m).trans ?_
  show ∑ i ∈ Finset.range N.R.m, F (i + 1) = ∑ l ∈ Finset.Icc 1 N.R.m, F l
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' F 0 N.R.m 1]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem toNat_floor_cast {q : ℚ} (hq : ∃ a : ℤ, q = a) (h0 : 0 ≤ q) : ((⌊q⌋.toNat : ℕ) : ℝ) = ((q : ℚ) : ℝ) := by
  obtain ⟨a, rfl⟩ := hq
  have ha : (0 : ℤ) ≤ a := by exact_mod_cast h0
  rw [Int.floor_intCast, Rat.cast_intCast]
  exact_mod_cast Int.toNat_of_nonneg ha

theorem k_two : 2 ≤ N.R.k := by
  have := N.R.m_add_three_le_k
  omega

theorem aT_int (t : N.R.A) : ∃ a : ℤ, N.aT t = a := by
  unfold aT
  obtain ⟨n, hn⟩ := (N.hc (false, t)).u_half ⟨0, by have := N.R.m_add_three_le_k; omega⟩
  obtain ⟨c, hc⟩ := N.R.k_even
  have hk : (N.R.k : ℚ) = 2 * c := by rw [hc]; push_cast; ring
  refine ⟨n + 1 - c, ?_⟩
  rw [hn, hk]
  push_cast
  ring

theorem bT_int (t : N.R.A) : ∃ a : ℤ, N.bT t = a := by
  unfold bT
  obtain ⟨n, hn⟩ := (N.hc (false, t)).u_half ⟨N.R.k - 1, by have := N.R.m_add_three_le_k; omega⟩
  obtain ⟨c, hc⟩ := N.R.k_even
  have hk : (N.R.k : ℚ) = 2 * c := by rw [hc]; push_cast; ring
  refine ⟨-n - c, ?_⟩
  rw [hn, hk]
  push_cast
  ring

theorem sN_cast (j : ℕ) (hj : 1 ≤ j) :
    (N.sN j : ℝ) = ((N.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((N.R.t : ℝ) + 1)) / 2 := by
  obtain ⟨a, ha⟩ := N.R.k_even
  obtain ⟨c, hc⟩ := N.R.t_odd
  unfold sN
  rw [ha, hc]
  have h1 : (a + a) / 2 = a := by omega
  have h2 : (2 * c + 1 + 1) / 2 = c + 1 := by omega
  rw [h1, h2]
  have h3 : ((2 * j - 1 : ℕ) : ℝ) = 2 * (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, h3]
  ring

theorem uW_zero (δ : Code N) (z : RPl N.R) (h : 0 < N.R.k) : N.uW δ z ⟨0, h⟩ = (N.hc z).u ⟨0, h⟩ := by
  unfold uW
  rw [dif_neg]
  rintro ⟨h1, -⟩
  simp at h1

theorem uW_last (δ : Code N) (z : RPl N.R) (h : N.R.k - 1 < N.R.k) :
    N.uW δ z ⟨N.R.k - 1, h⟩ = (N.hc z).u ⟨N.R.k - 1, h⟩ := by
  unfold uW
  rw [dif_neg]
  rintro ⟨-, h2⟩
  simp only [] at h2
  omega

theorem srcPar_lt (δ : Code N) (z : RPl N.R) (i : ℕ) (h : i < N.R.k) : N.srcPar δ z i = N.uW δ z ⟨i, h⟩ := by
  unfold srcPar
  rw [dif_pos h]

theorem x_pos : 0 < N.sc.x := lt_trans one_pos N.sc.one_lt_alt

theorem one_lt_L : 1 < N.sc.L := by
  show (1 : ℝ) < N.sc.x ^ N.sc.eps
  exact Real.one_lt_rpow N.sc.one_lt_alt N.sc.eps_pos

theorem b_pos : 0 < N.sc.b := by
  show (0 : ℝ) < Real.exp N.sc.L
  exact Real.exp_pos _

theorem one_le_b : 1 ≤ N.sc.b := by
  show (1 : ℝ) ≤ Real.exp N.sc.L
  exact Real.one_le_exp (le_of_lt (lt_trans zero_lt_one N.one_lt_L))

theorem a_pos : 0 < N.sc.a := by
  show (0 : ℝ) < N.sc.x * N.sc.b
  exact mul_pos N.x_pos N.b_pos

theorem b'_nonneg : 0 ≤ N.sc.b' := by
  show (0 : ℝ) ≤ N.sc.a / Real.exp (N.sc.x ^ (N.sc.eps / 3))
  exact div_nonneg (le_of_lt N.a_pos) (le_of_lt (Real.exp_pos _))

theorem one_le_rd : 1 ≤ N.rd := by
  show 1 ≤ N.H.rd
  first
  | (unfold Formalism.HC.HostRaw.rd
     apply Real.one_le_rpow _ (by positivity)
     have h := NumberField.discr_ne_zero N.H.E
     have : (1 : ℤ) ≤ |NumberField.discr N.H.E| := Int.one_le_abs h
     exact_mod_cast this)
  | (simp only [Formalism.HC.HostRaw.rd]
     apply Real.one_le_rpow _ (by positivity)
     have h := NumberField.discr_ne_zero N.H.E
     have : (1 : ℤ) ≤ |NumberField.discr N.H.E| := Int.one_le_abs h
     exact_mod_cast this)

theorem La_eq : N.La = Real.log N.sc.x + N.sc.L + Real.log N.rd := by
  have hrd : 0 < N.rd := lt_of_lt_of_le one_pos N.one_le_rd
  show Real.log (N.sc.x * Real.exp N.sc.L * N.rd) = _
  rw [Real.log_mul (mul_pos N.x_pos (Real.exp_pos _)).ne' hrd.ne',
    Real.log_mul N.x_pos.ne' (Real.exp_pos _).ne', Real.log_exp]

theorem one_le_La : 1 ≤ N.La := by
  rw [N.La_eq]
  have h1 : 0 < Real.log N.sc.x := Real.log_pos N.sc.one_lt_alt
  have h2 : 0 ≤ Real.log N.rd := Real.log_nonneg N.one_le_rd
  linarith [N.one_lt_L]

theorem Lp_nonneg : 0 ≤ N.Lp := by
  apply Real.log_nonneg
  show (1 : ℝ) ≤ N.sc.b * N.rd * ((N.g 0 : ℝ) * (N.g 1 : ℝ)) * (N.R.nV : ℝ)
  have hg0 : (1 : ℝ) ≤ (N.g 0 : ℝ) := by exact_mod_cast (N.g_prime 0).one_lt.le
  have hg1 : (1 : ℝ) ≤ (N.g 1 : ℝ) := by exact_mod_cast (N.g_prime 1).one_lt.le
  have hn : (1 : ℝ) ≤ (N.R.nV : ℝ) := by
    have : 1 ≤ N.R.nV := by
      obtain ⟨c, hc⟩ := N.R.t_odd
      unfold Ranks.nV
      omega
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ N.sc.b * N.rd := one_le_mul_of_one_le_of_one_le N.one_le_b N.one_le_rd
  have h2 : (1 : ℝ) ≤ (N.g 0 : ℝ) * (N.g 1 : ℝ) := one_le_mul_of_one_le_of_one_le hg0 hg1
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hn

theorem Nm_cast : (N.Nm : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by
  show ((N.R.k + N.R.m * (N.R.t + 1) : ℕ) : ℝ) = _
  push_cast
  ring

theorem N_le_Nm (j : ℕ) (h : j ≤ N.R.m) : N.R.N j ≤ N.Nm := by
  show N.R.k + j * (N.R.t + 1) ≤ N.R.k + N.R.m * (N.R.t + 1)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem nV_le_Nm : N.R.nV ≤ N.Nm := by
  show N.R.nV ≤ N.R.k + N.R.m * (N.R.t + 1)
  have h2 := N.R.two_le_m
  have h4 := N.R.three_m_lt_t
  have h3 : 2 * (N.R.t + 1) ≤ N.R.m * (N.R.t + 1) := Nat.mul_le_mul_right _ h2
  have h5 : N.R.r ≤ N.R.k + N.R.m := by
    first
    | (unfold Ranks.r; exact Nat.sub_le _ _)
    | (unfold Ranks.r; omega)
    | (simp only [Ranks.r]; omega)
  unfold Ranks.nV
  generalize N.R.m * (N.R.t + 1) = X at h3 ⊢
  omega

theorem eta_nonneg : 0 ≤ N.eta := by
  show (0 : ℝ) ≤ (N.R.m : ℝ) * (N.h0 : ℝ)
  positivity

theorem Sc_nonneg : 0 ≤ N.Sc := by
  show (0 : ℝ) ≤ (N.R.k : ℝ) * (4 * (N.Del : ℝ))
  positivity

theorem wN_cast {j : ℕ} (z : RPl N.R) (h0 : 0 ≤ N.w j z) : (N.wN j z : ℝ) = N.w j z := by
  have hq : ∃ a : ℤ, N.eQ j z = a := by
    unfold eQ
    split
    · first
      | exact (N.hc z).e_int _
      | (obtain ⟨a, ha⟩ := (N.hc z).e_int ⟨j - 1, by omega⟩; exact ⟨a, ha⟩)
    · exact ⟨0, by simp⟩
  have h0' : (0 : ℚ) ≤ N.eQ j z := by
    have : (0 : ℝ) ≤ ((N.eQ j z : ℚ) : ℝ) := h0
    exact_mod_cast this
  unfold wN
  exact toNat_floor_cast hq h0'

theorem nuN_cast (δ : Code N) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R) {i : ℕ} (hi : i < N.R.N (j - 1))
    (h0 : 0 ≤ N.nu δ j z i) : (N.nuN δ j z i : ℝ) = ((N.nu δ j z i : ℚ) : ℝ) := by
  unfold nuN
  first
  | exact toNat_floor_cast (N.nu_int δ j h1 h2 z i hi) h0
  | exact N.toNat_floor_cast (N.nu_int δ j h1 h2 z i hi) h0

theorem apN_cast {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R) {i : ℕ} (hi : i < (N.R.sigW j).1) :
    (N.apN j z i : ℝ) = ((N.aPlus j z i : ℚ) : ℝ) :=
  toNat_floor_cast (N.aPlus_int j z i) (le_trans zero_le_one (N.aPlus_ge_one j h1 h2 z i hi))

theorem phRows_nuRows (δ : Code N) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R)
    (h0 : ∀ i < N.R.N (j - 1), 0 ≤ N.nu δ j z i) :
    Formalism.DivisionValues.phRows (N.nuRows δ j z) = ∑ i, ph (N.nuPad δ j z i) := by
  have hle : N.R.N (j - 1) ≤ N.Nm := N.N_le_Nm (j - 1) (by omega)
  have h00 : ph 0 = 0 := by
    first
    | simp [Formalism.LatticeIndexTer.ph]
    | (unfold Formalism.LatticeIndexTer.ph; simp)
    | rfl
  unfold Formalism.DivisionValues.phRows nuRows nuPad
  rw [Multiset.map_map]
  refine Eq.trans (rfl : _ = ∑ i ∈ Finset.range (N.R.N (j - 1)), ph ((N.nuN δ j z i : ℕ) : ℝ)) ?_
  simp only [apply_ite ph, h00]
  refine Eq.trans ?_ (sum_pad (fun i => ph ((N.nu δ j z i : ℚ) : ℝ)) hle).symm
  exact Finset.sum_congr rfl (fun i hi => by
    rw [N.nuN_cast δ h1 h2 z (Finset.mem_range.1 hi) (h0 i (Finset.mem_range.1 hi))])

theorem sum_nuRows (δ : Code N) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N.R.m) (z : RPl N.R)
    (h0 : ∀ i < N.R.N (j - 1), 0 ≤ N.nu δ j z i) :
    (((N.nuRows δ j z).sum : ℕ) : ℝ) = ∑ i, N.nuPad δ j z i := by
  have hle : N.R.N (j - 1) ≤ N.Nm := N.N_le_Nm (j - 1) (by omega)
  have e : ((Multiset.range (N.R.N (j - 1))).map (N.nuN δ j z)).sum =
      ∑ i ∈ Finset.range (N.R.N (j - 1)), N.nuN δ j z i := rfl
  unfold nuRows nuPad
  rw [e, Nat.cast_sum]
  refine Eq.trans ?_ (sum_pad (fun i => ((N.nu δ j z i : ℚ) : ℝ)) hle).symm
  exact Finset.sum_congr rfl (fun i hi =>
    N.nuN_cast δ h1 h2 z (Finset.mem_range.1 hi) (h0 i (Finset.mem_range.1 hi)))

theorem sum_nuPad (δ : Code N) {j : ℕ} (hj : j ≤ N.R.m + 1) (z : RPl N.R) :
    ∑ i, N.nuPad δ j z i = ((N.nuAbs δ j z : ℚ) : ℝ) := by
  have hle : N.R.N (j - 1) ≤ N.Nm := N.N_le_Nm (j - 1) (by omega)
  unfold nuPad nuAbs
  refine (sum_pad (fun i => ((N.nu δ j z i : ℚ) : ℝ)) hle).trans ?_
  rw [Rat.cast_sum]

theorem sum_phPad (δ : Code N) {j : ℕ} (hj : j ≤ N.R.m + 1) (z : RPl N.R) :
    ∑ i, ph (N.nuPad δ j z i) = ∑ i ∈ Finset.range (N.R.N (j - 1)), ph ((N.nu δ j z i : ℚ) : ℝ) := by
  have hle : N.R.N (j - 1) ≤ N.Nm := N.N_le_Nm (j - 1) (by omega)
  have h0 : ph 0 = 0 := by
    first
    | simp [Formalism.LatticeIndexTer.ph]
    | (unfold Formalism.LatticeIndexTer.ph; simp)
    | rfl
  unfold nuPad
  simp only [apply_ite ph, h0]
  exact sum_pad (fun i => ph ((N.nu δ j z i : ℚ) : ℝ)) hle

end NumDatum

namespace NumDatum

variable (N : NumDatum)

theorem nuRows_split (δ : Code N) (j : ℕ) (z : RPl N.R) :
    N.nuRows δ (j + 1) z = Finset.univ.val.map (fun i : Fin (N.R.k - 2 + 2) => N.nuN δ (j + 1) z i.1) +
      (Multiset.range (N.R.N j - N.R.k)).map (fun c => N.nuN δ (j + 1) z (N.R.k + c)) := by
  unfold nuRows
  rw [univ_map_fin (N.R.k - 2 + 2) (N.nuN δ (j + 1) z)]
  have hk : N.R.k - 2 + 2 = N.R.k := by have := N.k_two; omega
  rw [hk]
  have hN : N.R.N (j + 1 - 1) = N.R.k + (N.R.N j - N.R.k) := by
    rw [Nat.add_sub_cancel]
    have : N.R.k ≤ N.R.N j := Nat.le_add_right _ _
    omega
  rw [hN, Multiset.range_add, Multiset.map_add, Multiset.map_map]
  rfl

theorem apRows_split (j : ℕ) (z : RPl N.R) :
    N.apRows (j + 1) z = Finset.univ.val.map (fun i : Fin (N.R.k - 2 + 1) => N.apN (j + 1) z i.1) +
      (Multiset.range (j + 1)).map (fun c => N.apN (j + 1) z (N.R.k - 1 + c)) := by
  unfold apRows
  rw [univ_map_fin (N.R.k - 2 + 1) (N.apN (j + 1) z)]
  have hk : N.R.k - 2 + 1 = N.R.k - 1 := by have := N.k_two; omega
  rw [hk]
  have hs : (N.R.sigW (j + 1)).1 = N.R.k - 1 + (j + 1) := by
    first
    | rfl
    | (simp [Ranks.sigW]; omega)
    | (unfold Ranks.sigW; simp; omega)
  rw [hs, Multiset.range_add, Multiset.map_add, Multiset.map_map]
  rfl

theorem stepE_num (δ : Code N) {Nc lam0 C0 ce Ch Sw C1 : ℝ} (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1)
    (j : Fin N.R.m) (ρ : RPl N.R) :
    N.eEN δ (j.1 + 1) ρ ≤
        C0 * (N.w (j.1 + 1) ρ + N.Sc + (N.Nm : ℝ) ^ 2 + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta) * N.La ∧
      |N.dN δ (j.1 + 1) ρ| ≤
        C0 * (N.w (j.1 + 1) ρ + (N.R.k : ℝ) * ((N.Nm : ℝ) + N.Sc) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta +
          (if ρ ∈ N.topsPl then (N.R.k : ℝ) * N.sc.b' else 0)) := by
  have hk2 := N.k_two
  have hm2 := N.R.two_le_m

  have hs : ∀ (j : Fin N.R.m) ρ, (N.sN (j.1 + 1) : ℝ) ≤ N.w (j.1 + 1) ρ := fun j ρ => by
    rw [N.sN_cast _ (by omega)]; exact H.sw _ (by omega) (by omega) ρ
  have hs0 : ∀ (j : Fin N.R.m), (0 : ℝ) ≤ N.sN (j.1 + 1) := fun _ => Nat.cast_nonneg _
  have hw : ∀ (j : Fin N.R.m) ρ, (N.wN (j.1 + 1) ρ : ℝ) = N.w (j.1 + 1) ρ := fun j ρ =>
    N.wN_cast ρ (le_trans (hs0 j) (hs j ρ))
  have hTop : ∀ ρ ∈ N.topsPl, ((⌊N.aT ρ.2⌋.toNat : ℕ) : ℝ) = N.aTPl ρ := fun ρ hρ => by
    rw [N.mem_topsPl] at hρ
    exact toNat_floor_cast (N.aT_int ρ.2) (H.top ρ.2 hρ.2).1
  have hmη : (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) * N.eta ≤ N.sc.a * N.rd := by
    have h1 := H.blkW
    have h2 := H.Nw
    have hN1 : (1 : ℝ) ≤ N.Nm := by
      have : 1 ≤ N.Nm := by unfold Nm Ranks.N; omega
      exact_mod_cast this
    have hb := N.one_le_b
    have hx := N.sc.one_lt_alt
    have hr := N.one_le_rd
    have h3 : N.sc.w'' N.R.n ≤ N.sc.b := by
      rcases le_or_gt 0 (N.sc.w'' N.R.n) with h | h
      · nlinarith
      · linarith
    have h4 : N.sc.b ≤ N.sc.a * N.rd := by
      show N.sc.b ≤ N.sc.x * N.sc.b * N.rd
      have : N.sc.b ≤ N.sc.x * N.sc.b := by nlinarith
      nlinarith
    linarith
  obtain ⟨eE, dd, h1, h2, h3, h4⟩ := Formalism.DivisionValues.rowsStepEOrigin (Fin N.R.m) (RPl N.R) N.topsPl (N.R.k - 2) N.R.t
    (fun j => j.1 + 1) (fun j => N.sN (j.1 + 1)) (fun ρ => ⌊N.aT ρ.2⌋.toNat) (fun ρ => ⌊N.bT ρ.2⌋.toNat)
    (fun j ρ => N.wN (j.1 + 1) ρ)
    (fun ρ i => ((N.uW δ ρ ⟨i.1, by have := i.2; omega⟩ : ℚ) : ℝ)) (fun ρ i => ((N.sigPar ρ i.1 : ℚ) : ℝ))
    (fun j ρ i => N.nuN δ (j.1 + 1) ρ i.1) (fun j ρ i => N.apN (j.1 + 1) ρ i.1)
    (fun j ρ => (Multiset.range (N.R.N j.1 - N.R.k)).map (fun c => N.nuN δ (j.1 + 1) ρ (N.R.k + c)))
    (fun j ρ => (Multiset.range (j.1 + 1)).map (fun c => N.apN (j.1 + 1) ρ (N.R.k - 1 + c)))
    (fun j ρ => N.nuRows δ (j.1 + 1) ρ) (fun j ρ => N.apRows (j.1 + 1) ρ) (fun j ρ => N.logHook (j.1 + 1) ρ)
    N.sc.a N.rd N.La N.R.k N.Nm N.Sc Sw N.eta N.R.m N.sc.b' C1 C0
    rfl N.one_le_La (by rw [Nat.cast_sub hk2]; ring) (Nat.cast_nonneg _) (le_of_eq N.Nm_cast.symm)
    N.b'_nonneg N.Sc_nonneg H.C1two H.constant_weight_sum_bound H.constant_succ_le (fun _ => by omega)
    (fun j => by have := j.2; exact_mod_cast (show j.1 + 1 ≤ N.R.m by omega))
    (fun j => N.sN_cast _ (by omega))
    (fun j ρ => by have := hs j ρ; rw [← hw j ρ] at this; exact_mod_cast this)
    (fun j ρ => by rw [hw j ρ]; exact H.rowsA _ (by omega) (by omega) ρ)
    hmη (by have := N.eta_nonneg; positivity)
    (fun j ρ hρ => by
      rw [hTop ρ hρ, hw j ρ]
      have hρ' := (N.mem_topsPl ρ).1 hρ
      have := H.topsA (j.1 + 1) (by omega) (by omega) ρ.2 hρ'.2
      have e : ρ = (false, ρ.2) := Prod.ext hρ'.1 rfl
      rw [e]
      exact this)
    (fun j ρ => N.hookLower_of Formalism.DivisionValues.rowsHook (j.1 + 1) (by omega) (by omega) ρ)
    (fun j ρ => N.nuRows_split δ j.1 ρ)
    (fun j ρ => N.apRows_split j.1 ρ)
    (fun j ρ i => by
      have hi : i.1 < N.R.N (j.1 + 1 - 1) := by
        rw [Nat.add_sub_cancel]; have := i.2; unfold Ranks.N; omega
      rw [N.nuN_cast δ (by omega) (by omega) ρ hi (H.nu0 _ (by omega) (by omega) ρ _ hi),
        N.nu_eq_originRow δ (j.1 + 1) (by omega) ρ i.1, N.srcPar_lt δ ρ i.1 (by have := i.2; omega), hw j ρ])
    (fun j ρ i => by
      have hi : i.1 < (N.R.sigW (j.1 + 1)).1 := by rw [sigW_fst]; have := i.2; omega
      rw [N.apN_cast (by omega) (by omega) ρ hi, N.aPlus_eq_originBig (j.1 + 1) ρ i.1, hw j ρ])
    (fun j ρ => by
      have hb := H.blk (j.1 + 1) (by omega) (by omega) ρ
      rw [Nat.add_sub_cancel] at hb
      rw [Nat.cast_multiset_sum, Multiset.map_map]
      refine le_trans (le_of_eq ?_) hb
      rw [Finset.sum_Ico_eq_sum_range]
      show ∑ c ∈ Finset.range (N.R.N j.1 - N.R.k), _ = _
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Function.comp_apply]
      have hc' : N.R.k + c < N.R.N (j.1 + 1 - 1) := by
        rw [Nat.add_sub_cancel]; have := Finset.mem_range.1 hc; omega
      exact N.nuN_cast δ (by omega) (by omega) ρ hc' (H.nu0 _ (by omega) (by omega) ρ _ hc'))
    (fun ρ i => by
      have := H.inter ρ i.1 (by have := i.2; omega)
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2)
    (fun ρ hρ => by
      have hρ' : ¬ (ρ.1 = false ∧ ρ.2 ∈ N.TT) := fun h => hρ ((N.mem_topsPl ρ).2 h)
      have := H.off ρ hρ'
      have e1 := N.uW_zero δ ρ (by omega)
      have e2 := N.uW_last δ ρ (by omega)
      constructor
      · show (0 : ℝ) ≤ ((N.uW δ ρ ⟨N.R.k - 2 + 1, _⟩ : ℚ) : ℝ) + ((N.R.k : ℝ) - 1) / 2
        have e3 : (⟨N.R.k - 2 + 1, by omega⟩ : Fin N.R.k) = ⟨N.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
        rw [e3, e2]
        exact_mod_cast this.1
      · show ((N.uW δ ρ ⟨0, _⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 ≤ Sw
        rw [e1]
        exact_mod_cast this.2)
    (fun ρ hρ => by
      have hρ' := (N.mem_topsPl ρ).1 hρ
      have e : ρ = (false, ρ.2) := Prod.ext hρ'.1 rfl
      obtain ⟨ha, hb, hv1, hv2⟩ := H.top ρ.2 hρ'.2
      have e1 := N.uW_zero δ ρ (by omega)
      have e2 := N.uW_last δ ρ (by omega)
      have e3 : (⟨N.R.k - 2 + 1, by omega⟩ : Fin N.R.k) = ⟨N.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · show ((N.uW δ ρ ⟨0, _⟩ : ℚ) : ℝ) = _
        rw [e1, toNat_floor_cast (N.aT_int ρ.2) ha]
        unfold aT
        rw [e]
        push_cast; ring
      · show ((N.uW δ ρ ⟨N.R.k - 2 + 1, _⟩ : ℚ) : ℝ) = _
        rw [e3, e2, toNat_floor_cast (N.bT_int ρ.2) hb]
        unfold bT
        rw [e]
        push_cast; ring
      · show (0 : ℝ) ≤ ((N.sigPar ρ (N.R.k - 2) : ℚ) : ℝ) + ((N.R.k : ℝ) - 2) / 2
        rw [e]; have h' := (Rat.cast_nonneg (K := ℝ)).2 hv1; push_cast [Nat.cast_sub hk2] at h' ⊢; linarith
      · show ((N.sigPar ρ 0 : ℚ) : ℝ) - ((N.R.k : ℝ) - 2) / 2 ≤ Sw
        rw [e]; have h' := hv2; push_cast [Nat.cast_sub hk2] at h' ⊢; linarith)
  have hj1 : 1 ≤ j.1 + 1 := by omega
  have hj2 : j.1 + 1 ≤ N.R.m := j.2
  have hnu := H.nu0 (j.1 + 1) hj1 hj2 ρ
  have hph := N.phRows_nuRows δ hj1 hj2 ρ hnu
  have hsum := N.sum_nuRows δ hj1 hj2 ρ hnu
  have ht : (if ρ ∈ N.topsPl then ph ((⌊N.aT ρ.2⌋.toNat : ℕ) : ℝ) else 0) =
      (if ρ ∈ N.topsPl then ph (N.aTPl ρ) else 0) := by
    split_ifs with h
    · rw [hTop ρ h]
    · rfl
  have ht' : (if ρ ∈ N.topsPl then ((⌊N.aT ρ.2⌋.toNat : ℕ) : ℝ) else 0) =
      (if ρ ∈ N.topsPl then N.aTPl ρ else 0) := by
    split_ifs with h
    · rw [hTop ρ h]
    · rfl
  have a1 := h1 j ρ
  have a2 := h2 j ρ
  have a3 := h3 j ρ
  have a4 := h4 j ρ
  rw [hph, ht] at a1
  rw [hsum, ht', hw j ρ] at a2
  rw [hw j ρ] at a3 a4
  constructor
  · unfold eEN
    linarith
  · have : N.dN δ (j.1 + 1) ρ = dd j ρ := by unfold dN; linarith
    rw [this]
    exact a4

end NumDatum

def RecNums.ofNum (N : NumDatum) {J : Type} [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1) : RecNums J (RPl N.R) where
  TT := N.topsPl
  logT := Real.log (T : ℝ)
  aT := N.aTPl
  r := N.Nm
  ν j ρ i := N.nuPad δ ((eJ j).1 + 1) ρ i
  logH j ρ := N.logHook ((eJ j).1 + 1) ρ
  x := N.sc.x
  eps := N.sc.eps
  L := N.sc.L
  b := N.sc.b
  a := N.sc.a
  rd := N.rd
  La := N.La
  B0 := N.B0
  Nc := Nc
  m := N.R.m
  f := N.R.f
  k := N.R.k
  Nn := N.Nm
  S := N.Sc
  tt := N.R.t
  η := N.eta
  w'' := N.sc.w'' N.R.n
  b' := N.sc.b'
  lam0 := lam0
  C0 := C0
  ce := ce
  Ch := Ch
  nV := N.R.nV
  Lp := N.Lp
  logOm := N.logOm
  pq j := ((N.R.k : ℝ) + (((eJ j).1 + 1 : ℕ) : ℝ) - 1) - ((N.R.m : ℝ) - (((eJ j).1 + 1 : ℕ) : ℝ))
  w j ρ := N.w ((eJ j).1 + 1) ρ
  eE j ρ := N.eEN δ ((eJ j).1 + 1) ρ
  δ j ρ := N.dN δ ((eJ j).1 + 1) ρ
  weight_height_sum_le j ρ := by unfold NumDatum.eEN; linarith
  weight_sum_eq j ρ := by unfold NumDatum.dN; ring
  p1 := N.sc.one_lt_alt
  p2 := N.sc.eps_pos
  p3 := rfl
  p4 := rfl
  p5 := rfl
  p6 := N.one_le_rd
  p7 := H.logrd
  p8 := H.logx
  p9 := rfl
  p10 := rfl
  p11 := H.Nc0
  p12 := by rw [Fintype.card_congr eJ, Fintype.card_fin]
  p13 := by
    have : Fintype.card (RPl N.R) = N.R.f := by
      simp [RPl, Fintype.card_prod, Formalism.HC.Frame.card_A, Ranks.f, Ranks.n]
    rw [this]
  p14 := by have := N.R.two_le_m; exact_mod_cast (show 1 ≤ N.R.m by omega)
  p15 := by
    have : 1 ≤ N.R.f := by unfold Ranks.f Ranks.n; have := N.R.ord_pos; omega
    exact_mod_cast this
  p16 := by have := N.k_two; exact_mod_cast (show 1 ≤ N.R.k by omega)
  p17 := by
    rw [N.Nm_cast]
    have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ N.R.m := Nat.cast_nonneg _
    nlinarith
  p18 := N.Sc_nonneg
  p19 := Nat.cast_nonneg _
  p20 := N.eta_nonneg
  p21 j ρ := by
    have h1 : 1 ≤ (eJ j).1 + 1 := by omega
    have h2 : (eJ j).1 + 1 ≤ N.R.m := (eJ j).2
    refine ⟨le_trans ?_ (H.sw _ h1 h2 ρ), H.w2b _ h1 h2 ρ⟩
    have : (1 : ℝ) ≤ (((eJ j).1 + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ N.R.k := Nat.cast_nonneg _
    apply div_nonneg _ (by norm_num)
    nlinarith
  p22 j := by
    have h1 : (1 : ℝ) ≤ (((eJ j).1 + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ (eJ j).1 + 1 by omega)
    have h2 : (((eJ j).1 + 1 : ℕ) : ℝ) ≤ N.R.m := by exact_mod_cast (eJ j).2
    rw [abs_le]
    constructor <;> linarith
  p23 := H.Om
  p24 := H.lam
  p25 := H.n2
  p26 := H.n3
  p27 := H.eta
  p28 := H.kN
  p29 := H.kS
  p30 := H.blkW
  p31 := H.Nw
  p32 := H.bN
  p33 := H.mkb
  p34 := N.b'_nonneg
  p35 := H.lam0
  p36 := Nat.cast_nonneg _
  p37 := by exact_mod_cast N.nV_le_Nm
  p38 := N.Lp_nonneg
  c1 := H.c1
  c2 := H.c2
  c3 := H.c3
  c4 := H.c4
  c5 := H.c5
  sE j ρ := by
    have := (N.stepE_num δ H (eJ j) ρ).1
    exact this
  sδ j ρ := by
    have := (N.stepE_num δ H (eJ j) ρ).2
    exact this

namespace RecNums

variable (N : NumDatum) {J : Type} [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
  (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1)

theorem ofNum_hA : (ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H).hA = N.hA Ch T := by
  unfold RecNums.hA NumDatum.hA
  simp only [ofNum, NumDatum.topsPl, Finset.sum_map, Finset.card_map]
  try rfl

theorem ofNum_hB (j : J) : (ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H).hB j = N.hB Ch δ ((eJ j).1 + 1) := by
  have hj : (eJ j).1 + 1 ≤ N.R.m + 1 := by have := (eJ j).2; omega
  unfold RecNums.hB NumDatum.hB
  rw [add_assoc]
  congr 1
  · apply Finset.sum_congr rfl
    intro ρ _
    show (∑ i, ph (N.nuPad δ ((eJ j).1 + 1) ρ i)) - (∑ i, N.nuPad δ ((eJ j).1 + 1) ρ i) * N.logOm = _
    unfold NumDatum.kerPlace
    rw [N.sum_phPad δ hj, N.sum_nuPad δ hj]
    try ring
  · show Ch * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * (N.La + (N.R.m : ℝ) ^ 3 * N.sc.L) = _
    ring

theorem ofNum_hX (j : J) : (ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H).hX j = N.hX Ch ((eJ j).1 + 1) := by
  unfold RecNums.hX NumDatum.hX
  simp only [ofNum]
  try rfl

theorem ofNum_hu : (ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H).hu = N.hU Ch δ T := by
  unfold RecNums.hu NumDatum.hU
  simp only [ofNum_hA, ofNum_hB, ofNum_hX]
  rw [Finset.sum_sub_distrib, N.sum_lifts (N.hB Ch δ) eJ, N.sum_lifts (N.hX Ch) eJ]
  ring

theorem ofNum_rhs : (ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H).rhs =
    N.mainT T + ((50 * C0 + 10) * ((N.TT.card : ℝ) * N.sc.a * N.La) +
      60 * ce * ((N.R.m : ℝ) * (N.sc.x ^ N.sc.eps * (N.B0 + Nc)))) := by
  unfold RecNums.rhs
  simp only [ofNum]
  unfold NumDatum.mainT
  simp only [NumDatum.topsPl, Finset.sum_map, Finset.card_map]
  try rfl

theorem ofNum_errB : (ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H).errB =
    ce * (N.R.m : ℝ) * (N.sc.x ^ N.sc.eps * (N.B0 + Nc)) := rfl

end RecNums

section Concrete

open NumberField IsDedekindDomain Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem FoOf_num {Bs : DefBase K} {Df0 : DefSide Bs} {Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {Nn : IndefNum Bs}
    (P : IndefCore Df0 Df1 Dc Sp Nn) (Nd : NumDatum) (eJ : Bs.J ≃ Fin Nd.R.m)
    (hF : ∀ y j, Nn.F0 y j = Nd.Fj ((eJ j).1 + 1) y) :
    FoOf P = ∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * Nd.Fj ((eJ j).1 + 1) y) := by
  first
  | (unfold FoOf; simp only [hF])
  | (simp only [FoOf, hF])
  | (unfold FoOf; simp [hF])

theorem division_height_bound_numeric [IsTotallyComplex K] (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH)
    (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ) (Nc lam0 C0 ce Ch Sw C1 : ℝ)
    (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputs Pk.core (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) u Nu sg) :
    DivClauses Pk.core (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) u Nu sg ∧
      (∃ cu : InfinitePlace K → ℝ, (∀ v, 0 < cu v ∧
          Formalism.HN.opNormAt (Pi.basisFun K (Fin ((Dc Pk.Zs).a u))) ((Dc Pk.Zs).Xc u) (Pi.basisFun K (Fin Pk.core.cols.D)).dualBasis
            (Formalism.HN.dualFrame Pk.core.cols.XE) v (Pk.core.cols.col.B u) ^ 2 ≤ cu v) ∧
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (cu v) = Nd.hU Ch δ Tl - meanLog Pk.core.cols.κ) ∧
      Pk.core.cols.muCC - meanLog Pk.core.cols.κ + Nd.hU Ch δ Tl - 2 * FoOf Pk.core ≤
        Nd.mainT Tl + ((50 * C0 + 10) * ((Nd.TT.card : ℝ) * Nd.sc.a * Nd.La) +
          60 * ce * ((Nd.R.m : ℝ) * (Nd.sc.x ^ Nd.sc.eps * (Nd.B0 + Nc)))) ∧
      ((∀ y j, (Zsc Pk.Zs).F0 y j = Nd.Fj ((eJ j).1 + 1) y) →
        Pk.core.cols.muCC - meanLog Pk.core.cols.κ + Nd.hU Ch δ Tl -
            2 * (∑ j, ∑ y ∈ Pk.core.base.Tw, lw y * ((ramw y : ℝ) * Nd.Fj ((eJ j).1 + 1) y)) ≤
          Nd.mainT Tl + ((50 * C0 + 10) * ((Nd.TT.card : ℝ) * Nd.sc.a * Nd.La) +
            60 * ce * ((Nd.R.m : ℝ) * (Nd.sc.x ^ Nd.sc.eps * (Nd.B0 + Nc))))) := by
  have hL := division_height_bound_clauses A hOk hsep P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H) u Nu sg I
  have hu := RecNums.ofNum_hu Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H
  have hr := RecNums.ofNum_rhs Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H
  have h2 := hL.2.1
  have h3 := hL.2.2.1
  rw [hu] at h2
  rw [hu, hr] at h3
  refine ⟨hL, h2, h3, fun hF => ?_⟩
  rw [← FoOf_num Pk.core Nd eJ hF]
  exact h3

end Concrete

namespace NumInst

open Formalism.BasicNotions.Examples₂

def hcUTop : Fin 8 → ℚ := ![113/2, 47/2, 39/2, 31/2, 23/2, 15/2, 7/2, -7/2]

def hcTop : HCParam R0 where
  u := hcUTop
  v := hcV
  b := hcB
  e := hcE
  u_gt_v := by
    intro i
    fin_cases i <;> simp [hcUTop, hcV] <;> norm_num
  v_gt_u := by
    intro i
    fin_cases i <;> simp [hcUTop, hcV] <;> norm_num
  u_last_gt := by
    intro h h'
    simp [hcUTop, hcB, R0]
    norm_num
  gap_be := hc0.gap_be
  gap_eb := hc0.gap_eb
  e_int := hc0.e_int
  u_half := by
    intro i
    fin_cases i
    · exact ⟨56, by simp [hcUTop]; norm_num⟩
    · exact ⟨23, by simp [hcUTop]; norm_num⟩
    · exact ⟨19, by simp [hcUTop]; norm_num⟩
    · exact ⟨15, by simp [hcUTop]; norm_num⟩
    · exact ⟨11, by simp [hcUTop]; norm_num⟩
    · exact ⟨7, by simp [hcUTop]; norm_num⟩
    · exact ⟨3, by simp [hcUTop]; norm_num⟩
    · exact ⟨-4, by simp [hcUTop]; norm_num⟩
  v_int := hc0.v_int
  b_int := hc0.b_int

def MBig : ℝ := 200 + |numEx.logOm|

theorem MBig_ge : 200 ≤ MBig := by
  unfold MBig
  linarith [abs_nonneg numEx.logOm]

def scBig : Scale where
  x := Real.exp (100 * MBig)
  eps := 1 / 100
  one_lt_alt := by have := Real.add_one_le_exp (100 * MBig); linarith [MBig_ge]
  eps_pos := by norm_num
  eps_lt := by norm_num
  J := 1
  one_le_J := le_rfl

def numBig : NumDatum where
  R := numEx.R
  sc := scBig
  H := numEx.H
  g := numEx.g
  g_prime := numEx.g_prime
  TT := numEx.TT
  Del := numEx.Del
  h0 := numEx.h0
  hc := fun z => if z = (false, 0) then hcTop else hc0

def wd0 : Code numBig := fun _ => false

theorem big_R : numBig.R = R0 := rfl
theorem big_logOm : numBig.logOm = numEx.logOm := rfl
theorem big_TT : numBig.TT = {0} := rfl

theorem big_hc_e (z : RPl numBig.R) : (numBig.hc z).e = hcE := by
  by_cases h : z = (false, 0)
  · show (if z = (false, 0) then hcTop else hc0).e = hcE
    rw [if_pos h]
    rfl
  · show (if z = (false, 0) then hcTop else hc0).e = hcE
    rw [if_neg h]
    first | rfl | simp [hc0] | decide

theorem big_hc_v (z : RPl numBig.R) : (numBig.hc z).v = hcV := by
  by_cases h : z = (false, 0)
  · show (if z = (false, 0) then hcTop else hc0).v = hcV
    rw [if_pos h]
    rfl
  · show (if z = (false, 0) then hcTop else hc0).v = hcV
    rw [if_neg h]
    first | rfl | simp [hc0] | decide

theorem big_L : numBig.sc.L = Real.exp MBig := by
  show Real.exp (100 * MBig) ^ (1 / 100 : ℝ) = Real.exp MBig
  rw [← Real.exp_mul]
  congr 1
  ring

theorem big_logx : Real.log numBig.sc.x = 100 * MBig := by
  show Real.log (Real.exp (100 * MBig)) = 100 * MBig
  exact Real.log_exp _

theorem big_X' : numBig.sc.X' = Real.exp (Real.exp (MBig / 3)) := by
  show Real.exp (Real.exp (100 * MBig) ^ ((1 / 100 : ℝ) / 3)) = Real.exp (Real.exp (MBig / 3))
  rw [← Real.exp_mul]
  congr 2
  ring

end NumInst

namespace NumInst

open Formalism.BasicNotions.Examples₂

@[simp] theorem big_k : numBig.R.k = 8 := rfl
@[simp] theorem big_m : numBig.R.m = 2 := rfl
@[simp] theorem large_parameter_sqrt_bound : numBig.R.t = 15 := rfl
@[simp] theorem big_e : numBig.R.e = 2 := rfl
@[simp] theorem big_nV : numBig.R.nV = 24 := rfl
@[simp] theorem big_Del : numBig.Del = 1 := rfl
@[simp] theorem large_example_height : numBig.h0 = 18 := rfl

theorem big_hc_top : numBig.hc (false, 0) = hcTop := by
  first
  | (show (if ((false, 0) : RPl numBig.R) = (false, 0) then hcTop else hc0) = hcTop
     exact if_pos rfl)
  | simp [numBig]

theorem big_hc_off (z : RPl numBig.R) (h : z ≠ (false, 0)) : numBig.hc z = hc0 := by
  first
  | (show (if z = (false, 0) then hcTop else hc0) = hc0
     exact if_neg h)
  | simp [numBig, h]

theorem big_Nm : (numBig.Nm : ℝ) = 40 := by
  rw [NumDatum.Nm_cast, big_k, big_m, large_parameter_sqrt_bound]
  norm_num
theorem big_Sc : numBig.Sc = 32 := by
  show ((numBig.R.k : ℕ) : ℝ) * (4 * ((numBig.Del : ℕ) : ℝ)) = 32
  rw [big_k, big_Del]
  norm_num
theorem big_eta : numBig.eta = 36 := by
  show ((numBig.R.m : ℕ) : ℝ) * ((numBig.h0 : ℕ) : ℝ) = 36
  rw [big_m, large_example_height]
  norm_num

theorem exp_cube {y : ℝ} (hy : 0 ≤ y) : y ^ 3 / 6 ≤ Real.exp y := by
  first
  | (have := Real.pow_div_factorial_le_exp hy 3
     norm_num [Nat.factorial] at this
     linarith)
  | (have := Real.pow_div_factorial_le_exp y hy 3
     norm_num [Nat.factorial] at this
     linarith)
  | (have h := Real.sum_le_exp_of_nonneg hy 4
     simp [Finset.sum_range_succ, Nat.factorial] at h
     nlinarith [sq_nonneg y, pow_nonneg hy 3])

theorem big_L_ge : 1000000 ≤ numBig.sc.L := by
  rw [big_L]
  have h := exp_cube (show (0 : ℝ) ≤ MBig by linarith [MBig_ge])
  have h2 : (200 : ℝ) ^ 3 / 6 ≤ MBig ^ 3 / 6 := by
    have := MBig_ge
    gcongr
  linarith [show (1000000 : ℝ) ≤ 200 ^ 3 / 6 by norm_num]

theorem big_b_ge : numBig.sc.L ^ 3 / 6 ≤ numBig.sc.b := by
  show numBig.sc.L ^ 3 / 6 ≤ Real.exp numBig.sc.L
  exact exp_cube (le_of_lt (lt_trans zero_lt_one numBig.one_lt_L))

theorem big_rd : 1 ≤ numBig.rd ∧ numBig.rd ≤ 72 := by
  refine ⟨numBig.one_le_rd, ?_⟩
  have h1 : numBig.rd ≤ ((16 : ℕ) : ℝ) / 2 * Real.sqrt (((11 : ℕ) : ℝ) * ((7 : ℕ) : ℝ)) := hostEx.der.rd_le
  have h2 : Real.sqrt (((11 : ℕ) : ℝ) * ((7 : ℕ) : ℝ)) ≤ 9 := by
    rw [show (9 : ℝ) = Real.sqrt (9 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3 : ((16 : ℕ) : ℝ) / 2 = 8 := by norm_num
  rw [h3] at h1
  linarith

theorem big_logrd : 0 ≤ Real.log numBig.rd ∧ Real.log numBig.rd ≤ 71 := by
  obtain ⟨h1, h2⟩ := big_rd
  exact ⟨Real.log_nonneg h1, by have := Real.log_le_sub_one_of_pos (by linarith : 0 < numBig.rd); linarith⟩

theorem big_y : 67 ≤ Real.exp (MBig / 3) := by
  have := Real.add_one_le_exp (MBig / 3)
  linarith [MBig_ge]

theorem big_Ly : numBig.sc.L = Real.exp (MBig / 3) ^ 3 := by
  rw [big_L, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem big_w'' : numBig.sc.w'' numBig.R.n = numBig.sc.b / (4 * numBig.sc.X') := by
  unfold Scale.w''
  have hn : numBig.R.n = 4 := by
    first
    | rfl
    | decide
    | simp [Ranks.n]
  rw [hn]
  have hx := numBig.x_pos
  have hX : 0 < numBig.sc.X' := Real.exp_pos _
  show numBig.sc.x * numBig.sc.b / numBig.sc.X' / (numBig.sc.x * ((4 : ℕ) : ℝ)) = numBig.sc.b / (4 * numBig.sc.X')
  field_simp
  try ring

theorem big_X'_ge : 67 ≤ numBig.sc.X' := by
  rw [big_X']
  have := Real.add_one_le_exp (Real.exp (MBig / 3))
  linarith [big_y]

theorem big_bX : 4608 * numBig.sc.X' ≤ numBig.sc.b := by
  have hy := big_y
  have hb : numBig.sc.b = Real.exp (Real.exp (MBig / 3) ^ 3) := by
    show Real.exp numBig.sc.L = _
    rw [big_Ly]
  rw [hb, big_X']
  have h1 : Real.exp (Real.exp (MBig / 3) ^ 3) =
      Real.exp (Real.exp (MBig / 3)) * Real.exp (Real.exp (MBig / 3) ^ 3 - Real.exp (MBig / 3)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h1]
  have h3 : (4488 : ℝ) ≤ Real.exp (MBig / 3) ^ 2 - 1 := by nlinarith
  have h2 : (4608 : ℝ) ≤ Real.exp (Real.exp (MBig / 3) ^ 3 - Real.exp (MBig / 3)) := by
    have := Real.add_one_le_exp (Real.exp (MBig / 3) ^ 3 - Real.exp (MBig / 3))
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (MBig / 3) - 67)
      (by linarith : (0 : ℝ) ≤ Real.exp (MBig / 3) ^ 2 - 1 - 4488)]
  have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (Real.exp (MBig / 3))).le
  linarith

theorem big_w''_ge : 1152 ≤ numBig.sc.w'' numBig.R.n := by
  rw [big_w'']
  have hX : 0 < numBig.sc.X' := lt_of_lt_of_le (by norm_num) big_X'_ge
  have h4 : (0 : ℝ) < 4 * numBig.sc.X' := by linarith
  first
  | (rw [le_div_iff₀ h4]; linarith [big_bX])
  | (rw [le_div_iff h4]; linarith [big_bX])

theorem big_Nw : (numBig.Nm : ℝ) * numBig.sc.w'' numBig.R.n ≤ numBig.sc.b := by
  rw [big_Nm, big_w'']
  have hX : 0 < numBig.sc.X' := lt_of_lt_of_le (by norm_num) big_X'_ge
  have hb := numBig.b_pos
  have e : (40 : ℝ) * (numBig.sc.b / (4 * numBig.sc.X')) = numBig.sc.b * (10 / numBig.sc.X') := by ring
  rw [e]
  have h10 : 10 / numBig.sc.X' ≤ 1 := by
    rw [div_le_one hX]
    linarith [big_X'_ge]
  calc numBig.sc.b * (10 / numBig.sc.X') ≤ numBig.sc.b * 1 := mul_le_mul_of_nonneg_left h10 hb.le
    _ = numBig.sc.b := mul_one _

theorem big_b'X : numBig.sc.b' * numBig.sc.X' = numBig.sc.a := by
  show numBig.sc.a / numBig.sc.X' * numBig.sc.X' = numBig.sc.a
  exact div_mul_cancel₀ _ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 67) big_X'_ge).ne'

theorem big_b'_le {c : ℝ} (hc : c ≤ 67) : numBig.sc.b' * c ≤ numBig.sc.a := by
  calc numBig.sc.b' * c ≤ numBig.sc.b' * numBig.sc.X' :=
        mul_le_mul_of_nonneg_left (le_trans hc big_X'_ge) numBig.b'_nonneg
    _ = numBig.sc.a := big_b'X

theorem big_x_ge : 1000000000000 ≤ numBig.sc.x := by
  show (1000000000000 : ℝ) ≤ Real.exp (100 * MBig)
  have h := exp_cube (show (0 : ℝ) ≤ 100 * MBig by linarith [MBig_ge])
  have h2 : (20000 : ℝ) ^ 3 / 6 ≤ (100 * MBig) ^ 3 / 6 := by
    have : (20000 : ℝ) ≤ 100 * MBig := by linarith [MBig_ge]
    gcongr
  linarith [show (1000000000000 : ℝ) ≤ 20000 ^ 3 / 6 by norm_num]

theorem big_La : numBig.La = 100 * MBig + numBig.sc.L + Real.log numBig.rd := by
  rw [NumDatum.La_eq, big_logx]

theorem large_example_exponent_zero : numBig.aT 0 = 53 := by
  unfold NumDatum.aT
  have e0 : ∀ h, (numBig.hc (false, 0)).u ⟨0, h⟩ = 113 / 2 := by
    intro h
    first | rfl | (rw [big_hc_top]; rfl) | decide
  rw [e0]
  norm_num

theorem large_example_bound_zero : numBig.bT 0 = 0 := by
  unfold NumDatum.bT
  have e7 : ∀ h, (numBig.hc (false, 0)).u ⟨numBig.R.k - 1, h⟩ = -7 / 2 := by
    intro h
    first | rfl | (rw [big_hc_top]; rfl) | decide
  rw [e7]
  norm_num

theorem big_eQ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2) (z : RPl numBig.R) :
    numBig.eQ j z = if j = 1 then 100 else 118 := by
  unfold NumDatum.eQ
  rw [dif_pos ⟨h1, h2⟩, big_hc_e]
  interval_cases j <;> first | rfl | simp [hcE] | norm_num [hcE]

theorem big_w (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2) (z : RPl numBig.R) : 100 ≤ numBig.w j z ∧ numBig.w j z ≤ 118 := by
  unfold NumDatum.w
  rw [big_eQ j h1 h2 z]
  split_ifs <;> norm_num

end NumInst

namespace NumInst

open Formalism.BasicNotions.Examples₂

theorem hcV_nonneg (l : Fin 7) : 0 ≤ hcV l := by
  first
  | (fin_cases l <;> norm_num [hcV])
  | (fin_cases l <;> simp [hcV])

theorem big_v_nonneg (z : RPl numBig.R) (l : Fin (numBig.R.k - 1)) : 0 ≤ (numBig.hc z).v l := by
  rw [big_hc_v]
  exact hcV_nonneg l

theorem big_uW_ge (z : RPl numBig.R) (i : Fin numBig.R.k) : -7 / 2 ≤ numBig.uW wd0 z i := by
  unfold NumDatum.uW
  by_cases h : 1 ≤ i.1 ∧ i.1 + 1 < numBig.R.k
  · rw [dif_pos h, if_neg (by simp [wd0])]
    have := big_v_nonneg z ⟨i.1 - 1, by have := i.2; omega⟩
    linarith
  · rw [dif_neg h]
    by_cases hz : z = (false, 0)
    · have hu : ∀ l : Fin 8, -7 / 2 ≤ hcUTop l := by intro l; fin_cases l <;> simp [hcUTop] <;> norm_num
      rw [hz, big_hc_top]
      exact hu i
    · have hu : ∀ l : Fin 8, -7 / 2 ≤ hcU l := by intro l; fin_cases l <;> simp [hcU] <;> norm_num
      rw [big_hc_off z hz]
      exact hu i

theorem big_N (j : ℕ) (hj : j ≤ 2) : (numBig.R.N j : ℚ) ≤ 40 := by
  have : numBig.R.N j ≤ 40 := by
    show numBig.R.k + j * (numBig.R.t + 1) ≤ 40
    rw [big_k, large_parameter_sqrt_bound]
    omega
  exact_mod_cast this

theorem big_nu_first (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2) (z : RPl numBig.R) (i : ℕ) (hi : i < 8) :
    0 ≤ numBig.nu wd0 j z i := by
  have hu := big_uW_ge z ⟨i, hi⟩
  unfold NumDatum.nu
  rw [NumDatum.srcPar_lt numBig wd0 z i hi, big_eQ j h1 h2 z]
  have h2' : j ≤ 2 := h2
  have hi' : (i : ℚ) ≤ 7 := by exact_mod_cast (show i ≤ 7 by omega)
  have hi0 : (0 : ℚ) ≤ i := by positivity
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · have e1 : numBig.R.N (1 - 1) = 8 := rfl
    have e2 : numBig.R.N 1 = 24 := rfl
    rw [e1, e2]
    norm_num
    linarith
  · have e1 : numBig.R.N (2 - 1) = 24 := rfl
    have e2 : numBig.R.N 2 = 40 := rfl
    rw [e1, e2]
    norm_num
    linarith

theorem big_nu_blk (z : RPl numBig.R) (c : ℕ) (hc : c < 16) : numBig.nu wd0 2 z (8 + c) = 2 := by
  have hk : numBig.R.k = 8 := rfl
  have ht : numBig.R.t = 15 := rfl
  unfold NumDatum.nu NumDatum.srcPar
  rw [dif_neg (by rw [hk]; omega)]
  rw [dif_pos (by show (8 + c - 8) / (15 + 1) < 2; omega)]
  have hq : (8 + c - numBig.R.k) / (numBig.R.t + 1) = 0 := by
    show (8 + c - 8) / (15 + 1) = 0
    omega
  have hr : (8 + c - numBig.R.k) % (numBig.R.t + 1) = c := by
    show (8 + c - 8) % (15 + 1) = c
    omega
  have he : ∀ h, (numBig.hc z).e ⟨(8 + c - numBig.R.k) / (numBig.R.t + 1), h⟩ = 100 := by
    intro h
    rw [big_hc_e]
    simp only [hq]
    rfl
  rw [he, hr, big_eQ 2 (by norm_num) (by norm_num) z]
  have hN1 : numBig.R.N (2 - 1) = 24 := rfl
  have hN2 : numBig.R.N 2 = 40 := rfl
  rw [hN1, hN2, ht]
  norm_num
  ring

theorem large_example_weight_nonneg (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ numBig.R.m) (z : RPl numBig.R) (i : ℕ) (hi : i < numBig.R.N (j - 1)) :
    0 ≤ numBig.nu wd0 j z i := by
  have h2' : j ≤ 2 := h2
  by_cases hi8 : i < 8
  · exact big_nu_first j h1 h2' z i hi8
  · have hj2 : j = 2 := by
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
      · have e : numBig.R.N (1 - 1) = 8 := rfl
        rw [e] at hi
        omega
      · rfl
    subst hj2
    have e : numBig.R.N (2 - 1) = 24 := rfl
    rw [e] at hi
    have := big_nu_blk z (i - 8) (by omega)
    rw [show 8 + (i - 8) = i by omega] at this
    rw [this]
    norm_num

theorem big_blk (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ numBig.R.m) (z : RPl numBig.R) :
    (∑ i ∈ Finset.Ico numBig.R.k (numBig.R.N (j - 1)), ((numBig.nu wd0 j z i : ℚ) : ℝ)) ≤
      (numBig.R.m : ℝ) * ((numBig.R.t : ℝ) + 1) * numBig.eta := by
  rw [big_eta]
  have hm : ((numBig.R.m : ℕ) : ℝ) = 2 := by rw [big_m]; norm_num
  have ht : ((numBig.R.t : ℕ) : ℝ) = 15 := by rw [large_parameter_sqrt_bound]; norm_num
  rw [hm, ht]
  have h2' : j ≤ 2 := h2
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · have e : numBig.R.N (1 - 1) = 8 := rfl
    rw [big_k, e, Finset.Ico_self, Finset.sum_empty]
    norm_num
  · have e : numBig.R.N (2 - 1) = 24 := rfl
    rw [big_k, e]
    have hc : ∀ i ∈ Finset.Ico 8 24, ((numBig.nu wd0 2 z i : ℚ) : ℝ) = 2 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have := big_nu_blk z (i - 8) (by omega)
      rw [show 8 + (i - 8) = i by omega] at this
      rw [this]
      norm_num
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico]
    norm_num

theorem big_inter (z : RPl numBig.R) (i : ℕ) (h : i + 1 < numBig.R.k) :
    numBig.sigPar z i < numBig.uW wd0 z ⟨i, by omega⟩ ∧ numBig.uW wd0 z ⟨i + 1, h⟩ < numBig.sigPar z i := by
  have hi : i < 7 := by simp at h; omega
  unfold NumDatum.sigPar NumDatum.uW
  rw [dif_pos (show i < numBig.R.k - 1 by simp; omega), big_hc_v]
  by_cases hz : z = (false, 0)
  · rw [hz, big_hc_top]
    interval_cases i <;> simp [hcTop, hcUTop, hcV, wd0] <;> norm_num
  · rw [big_hc_off z hz]
    interval_cases i <;> simp [hc0, hcU, hcV, wd0] <;> norm_num

theorem big_off (z : RPl numBig.R) (hz : ¬ (z.1 = false ∧ z.2 ∈ numBig.TT)) :
    0 ≤ (numBig.hc z).u ⟨numBig.R.k - 1, by have := numBig.R.m_add_three_le_k; omega⟩ + ((numBig.R.k : ℚ) - 1) / 2 ∧
    (((numBig.hc z).u ⟨0, by have := numBig.R.m_add_three_le_k; omega⟩ - ((numBig.R.k : ℚ) - 1) / 2 : ℚ) : ℝ) ≤ 53 := by
  have hz' : z ≠ (false, 0) := by
    intro h
    apply hz
    rw [h]
    exact ⟨rfl, by rw [big_TT]; exact Finset.mem_singleton_self _⟩
  have e0 : ∀ h, (numBig.hc z).u ⟨0, h⟩ = 113 / 2 := by
    intro h
    rw [big_hc_off z hz']
    first | rfl | decide
  have e7 : ∀ h, (numBig.hc z).u ⟨numBig.R.k - 1, h⟩ = -1 / 2 := by
    intro h
    rw [big_hc_off z hz']
    first | rfl | decide
  rw [e0, e7]
  constructor <;> norm_num

theorem big_top (t : numBig.R.A) (ht : t ∈ numBig.TT) :
    0 ≤ numBig.aT t ∧ 0 ≤ numBig.bT t ∧
    0 ≤ numBig.sigPar (false, t) (numBig.R.k - 2) + ((numBig.R.k : ℚ) - 2) / 2 ∧
    ((numBig.sigPar (false, t) 0 - ((numBig.R.k : ℚ) - 2) / 2 : ℚ) : ℝ) ≤ 53 := by
  rw [big_TT, Finset.mem_singleton] at ht
  subst ht
  refine ⟨by rw [large_example_exponent_zero]; norm_num, by rw [large_example_bound_zero], ?_, ?_⟩
  · unfold NumDatum.sigPar
    rw [dif_pos (by simp), big_hc_v]
    simp [hcV]
    norm_num
  · unfold NumDatum.sigPar
    rw [dif_pos (by simp), big_hc_v]
    simp [hcV]
    norm_num

theorem big_bL : 12800 * numBig.sc.L ≤ numBig.sc.b ∧ 1000000 ≤ numBig.sc.b := by
  have hL := big_L_ge
  have hb := big_b_ge
  have h2 : (1000000 : ℝ) * numBig.sc.L ≤ numBig.sc.L ^ 2 := by nlinarith
  have h3 : (1000000 : ℝ) * numBig.sc.L ^ 2 ≤ numBig.sc.L ^ 3 := by nlinarith
  constructor <;> nlinarith

theorem big_ard : numBig.sc.b ≤ numBig.sc.a * numBig.rd := by
  have hb := numBig.b_pos
  have hx := numBig.sc.one_lt_alt
  have hrd := numBig.one_le_rd
  show numBig.sc.b ≤ numBig.sc.x * numBig.sc.b * numBig.rd
  have h1 : numBig.sc.b * 1 ≤ numBig.sc.b * numBig.sc.x := mul_le_mul_of_nonneg_left hx.le hb.le
  have h2 : numBig.sc.x * numBig.sc.b * 1 ≤ numBig.sc.x * numBig.sc.b * numBig.rd :=
    mul_le_mul_of_nonneg_left hrd (mul_pos numBig.x_pos hb).le
  nlinarith

theorem big_g : ((numBig.g 0 : ℕ) : ℝ) * ((numBig.g 1 : ℕ) : ℝ) * (numBig.R.nV : ℝ) ≤ numBig.sc.x := by
  have hx := big_x_ge
  have h0 : numBig.g 0 = 3697 := rfl
  have h1 : numBig.g 1 = 7393 := rfl
  rw [h0, h1, big_nV]
  norm_num
  linarith

theorem big_Lp : numBig.Lp ≤ numBig.La := by
  have hb := numBig.b_pos
  have hrd : 0 < numBig.rd := lt_of_lt_of_le one_pos numBig.one_le_rd
  have hg0 : (0 : ℝ) < (numBig.g 0 : ℝ) := by exact_mod_cast (numBig.g_prime 0).pos
  have hg1 : (0 : ℝ) < (numBig.g 1 : ℝ) := by exact_mod_cast (numBig.g_prime 1).pos
  have hn : (0 : ℝ) < (numBig.R.nV : ℝ) := by rw [big_nV]; norm_num
  have hg := big_g
  have hpos : 0 < numBig.sc.b * numBig.rd * ((numBig.g 0 : ℝ) * (numBig.g 1 : ℝ)) * (numBig.R.nV : ℝ) :=
    mul_pos (mul_pos (mul_pos hb hrd) (mul_pos hg0 hg1)) hn
  have hle : numBig.sc.b * numBig.rd * ((numBig.g 0 : ℝ) * (numBig.g 1 : ℝ)) * (numBig.R.nV : ℝ) ≤
      numBig.sc.x * numBig.sc.b * numBig.rd := by
    have hbr : 0 < numBig.sc.b * numBig.rd := mul_pos hb hrd
    calc _ = (numBig.sc.b * numBig.rd) * ((numBig.g 0 : ℝ) * (numBig.g 1 : ℝ) * (numBig.R.nV : ℝ)) := by ring
      _ ≤ (numBig.sc.b * numBig.rd) * numBig.sc.x := mul_le_mul_of_nonneg_left hg hbr.le
      _ = _ := by ring
  unfold NumDatum.Lp NumDatum.La
  first
  | exact Real.log_le_log hpos hle
  | exact Real.log_le_log_of_le hpos hle

theorem numFactsBig : numBig.NumFacts wd0 1 1 5 5 1 53 4 where
  logrd := by linarith [big_logrd.2, big_L_ge]
  logx := by
    rw [big_logx, big_L]
    have h := exp_cube (show (0 : ℝ) ≤ MBig by linarith [MBig_ge])
    have hM := MBig_ge
    have h2 : (40000 : ℝ) ≤ MBig ^ 2 := by nlinarith
    have h3 : MBig ^ 3 = MBig * MBig ^ 2 := by ring
    nlinarith
  Nc0 := by norm_num
  w2b j h1 h2 z := by linarith [(big_w j h1 (by simpa using h2) z).2, big_bL.2]
  Om := by
    rw [big_logOm, big_La]
    have := big_logrd.1
    have := big_L_ge
    have : |numEx.logOm| ≤ MBig := by unfold MBig; linarith
    linarith [MBig_ge]
  lam := by simp; linarith [big_bL.2]
  lam0 := by norm_num
  n2 := by rw [big_Nm]; linarith [big_bL.2]
  n3 := by rw [big_Nm]; simp; linarith [big_bL.1]
  eta := by rw [big_Nm, big_eta]; simp; linarith [big_bL.1, big_L_ge]
  kN := by rw [big_Nm]; simp; linarith [big_bL.2]
  kS := by rw [big_Sc]; simp; linarith [big_w''_ge]
  blkW := by rw [big_eta]; simp; linarith [big_w''_ge]
  Nw := big_Nw
  bN := by rw [big_Nm]; exact big_b'_le (by norm_num)
  mkb := by
    have := big_b'_le (c := 16) (by norm_num)
    simp; linarith
  c1 := by norm_num
  c2 := le_rfl
  c3 := by norm_num
  c4 := by norm_num
  c5 := by
    have := big_Lp
    have := numBig.one_le_La
    linarith
  C1two := by norm_num
  constant_weight_sum_bound := by rw [big_Sc]; norm_num
  constant_succ_le := by norm_num
  sw j h1 h2 z := by
    have hw := (big_w j h1 (by simpa using h2) z).1
    have hj : (j : ℝ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by simpa using h2)
    simp
    linarith
  rowsA j h1 h2 z := by linarith [(big_w j h1 (by simpa using h2) z).2, big_ard, big_bL.2]
  topsA j h1 h2 t ht := by
    rw [big_TT, Finset.mem_singleton] at ht
    subst ht
    rw [large_example_exponent_zero]
    push_cast
    linarith [(big_w j h1 (by simpa using h2) (false, 0)).2, big_ard, big_bL.2]
  nu0 := large_example_weight_nonneg
  blk := big_blk
  inter := big_inter
  off := big_off
  top := big_top

def recBig : RecNums (Fin 2) (RPl numBig.R) :=
  RecNums.ofNum numBig (Equiv.refl _) wd0 3 1 1 5 5 1 53 4 numFactsBig

end NumInst

end Formalism.L2.DIV
