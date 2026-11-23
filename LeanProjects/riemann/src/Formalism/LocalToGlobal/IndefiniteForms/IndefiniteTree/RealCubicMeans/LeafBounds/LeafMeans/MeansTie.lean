import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansPf
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

noncomputable section

open Finset

namespace IxMeans.MeansTie

def kap (N p : ℕ) (i : Fin N) : ℝ :=
  if (i : ℕ) < p then (N : ℝ) - 2 * p + 1 + 2 * (i : ℕ) else -(2 * (p : ℝ)) - N + 1 + 2 * (i : ℕ)

def de (N p : ℕ) (i : Fin N) : ℝ := if (i : ℕ) < p then 0 else -1

def gap {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k + 1 < N then v ⟨k, by omega⟩ - v ⟨k + 1, h⟩ else 0

def anchored {N : ℕ} (G : ℕ → ℝ) (A : ℕ) (i : Fin N) : ℝ :=
  if (i : ℕ) ≤ A then ∑ k ∈ Ico (i : ℕ) A, G k else -∑ k ∈ Ico A (i : ℕ), G k

def uMinus (N p : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := fun i => u i - c0 * de N p i

def firstVectorGaps (N p T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) (k : ℕ) : ℝ :=
  ((⌊gap (fun i => uMinus N p c0 u i - kap N p i) k / ((T : ℝ) + D + 1)⌋ : ℤ) : ℝ)

def firstGapVector (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := anchored (firstVectorGaps N p T D c0 u) A

def upDef (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  fun i => firstGapVector N p A T D c0 u i - 3 * N * de N p i

theorem anchored_gap {N : ℕ} (G : ℕ → ℝ) (A k : ℕ) (h : k + 1 < N) :
    anchored (N := N) G A ⟨k, by omega⟩ - anchored G A ⟨k + 1, h⟩ = G k := by
  unfold anchored
  dsimp only
  by_cases h1 : k + 1 ≤ A
  · have h0 : k ≤ A := by omega
    rw [if_pos h0, if_pos h1, Finset.sum_eq_sum_Ico_succ_bot (by omega : k < A)]
    ring
  · by_cases h0 : k ≤ A
    · have hk : A = k := by omega
      subst hk
      rw [if_pos h0, if_neg h1]
      simp
    · rw [if_neg h0, if_neg h1, Finset.sum_Ico_succ_top (by omega : A ≤ k)]
      ring

theorem anchored_anchor {N : ℕ} (G : ℕ → ℝ) (A : ℕ) (h : A < N) : anchored (N := N) G A ⟨A, h⟩ = 0 := by
  unfold anchored
  dsimp only
  simp

theorem first_gap_vector_difference (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) (k : ℕ) (h : k + 1 < N) :
    firstGapVector N p A T D c0 u ⟨k, by omega⟩ - firstGapVector N p A T D c0 u ⟨k + 1, h⟩ =
      ((⌊((u ⟨k, by omega⟩ - c0 * de N p ⟨k, by omega⟩ - kap N p ⟨k, by omega⟩) -
          (u ⟨k + 1, h⟩ - c0 * de N p ⟨k + 1, h⟩ - kap N p ⟨k + 1, h⟩)) / ((T : ℝ) + D + 1)⌋ : ℤ) : ℝ) := by
  unfold firstGapVector
  rw [anchored_gap _ _ _ h]
  unfold firstVectorGaps gap uMinus
  rw [dif_pos h]

theorem first_gap_vector_anchored (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) (h : A < N) :
    firstGapVector N p A T D c0 u ⟨A, h⟩ = 0 := anchored_anchor _ _ h

theorem upDef_blocks (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) (i : Fin N) :
    upDef N p A T D c0 u i = firstGapVector N p A T D c0 u i + if (i : ℕ) < p then 0 else 3 * N := by
  unfold upDef de
  split_ifs <;> push_cast <;> ring

theorem kap_gap_compact (N p k : ℕ) (h : k + 1 < N) (hk : k + 1 ≠ p) :
    kap N p ⟨k, by omega⟩ - kap N p ⟨k + 1, h⟩ = -2 := by
  unfold kap
  dsimp only
  split_ifs with h1 h2 h2
  · push_cast; ring
  · omega
  · omega
  · push_cast; ring

theorem kap_gap_bar (N p k : ℕ) (h : k + 1 < N) (hk : k + 1 = p) :
    kap N p ⟨k, by omega⟩ - kap N p ⟨k + 1, h⟩ = 2 * N - 2 := by
  unfold kap
  dsimp only
  rw [if_pos (by omega), if_neg (by omega)]
  subst hk
  push_cast
  ring

structure Leaves (Tau : Type) where

  dE : ℕ

  level : ℕ

  q1 : ℕ

  d : ℕ

  g1 : ℕ

  g2 : ℕ

  rr : ℕ

  rr' : ℕ

  r0 : ℕ

  P0 : ℝ

  logmu : ℝ

  cubicPeriodConstant : ℝ

  c1 : ℝ

  Nc : ℕ

  bigp : Tau → ℕ

  A : ℕ

  eloc : ℕ → Finset ℝ

def cppDef (q : ℕ) : ℝ := if q = 2 then 1 else 1 / ((q : ℝ) - 1)

def XWDef {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) : ℝ :=
  66 * P.L + (P.nc : ℝ) * P.f * P.N * Real.log P.rd

def kpDef {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) (q : ℕ) : ℝ :=
  (P.nc : ℝ) * P.f * P.N * P.vdd q / 2

namespace Leaves

variable {Tau ι : Type} [Fintype Tau] [Fintype ι] (Lv : Leaves Tau) (P : MeansPack Tau ι)

def rdDef : ℝ := (Lv.dE : ℝ) ^ ((1 : ℝ) / (2 * (P.f : ℝ)))

def vddDef (q : ℕ) : ℝ := (padicValNat q Lv.dE : ℝ) / (2 * (P.f : ℝ))

def SBDef : Finset ℕ := ((range (⌊P.B0⌋₊ + 1)).filter Nat.Prime) ∪ (2 * Lv.dE * Lv.level).primeFactors

def PPeDef : ℝ :=
  3 / 2 * (P.f : ℝ) * (P.N : ℝ) ^ 4 * P.L
    + (((P.f : ℝ) * (P.N : ℝ) ^ 2 + 3) * P.f * P.N * Real.log P.rd + 3 * Real.log ((2 * Lv.q1 * Lv.d : ℕ) : ℝ))
    + (3 * Real.log ((Lv.g1 * Lv.g2 : ℕ) : ℝ) + Real.log ((Lv.rr * Lv.rr' : ℕ) : ℝ))

def Xde : ℝ := Lv.logmu + 3 * (P.D : ℝ) * P.L

def Psup : ℝ := 1 / 2 * Real.log (Lv.r0 : ℝ) + Lv.P0 + 2 * (P.f : ℝ) * (P.N : ℝ) ^ 2

def Ptau0 : ℝ := 1 / 2 * Real.log (Lv.r0 : ℝ) + Real.log (Real.exp (Lv.Xde P) + 1) + Lv.Psup P

def PPA : ℝ := 3 * (P.D : ℝ) + 3 * Lv.cubicPeriodConstant

def PinfDef : ℝ :=
  2 * Lv.Ptau0 P + Lv.PPA P + 2 * (P.f : ℝ) * P.N * Lv.c1 + 7 * (P.f : ℝ) * (P.N : ℝ) ^ 2 + 2 * Real.log (Lv.Nc : ℝ)

def rnd (q : ℕ) : ℝ :=
  (if q ∣ 2 * Lv.dE * Lv.level then 1 else 0) + (if q ∣ 2 * Lv.q1 * Lv.d then kpDef P q + 1 else 0)

def eDef (q : ℕ) : ℝ := (Lv.eloc q).fold max 0 (fun x => x + Lv.rnd P q)

end Leaves

variable {Tau ι : Type} [Fintype Tau] [Fintype ι]

structure DefTie (P : MeansPack Tau ι) (Lv : Leaves Tau) : Prop where
  hu1 : ∀ τ, P.u1 τ = firstGapVector P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
  hup : ∀ τ, P.up τ = upDef P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
  hrd : P.rd = Lv.rdDef P
  hvdd : ∀ q, P.vdd q = Lv.vddDef P q
  hcpp : ∀ q, P.cpp q = cppDef q
  hSB : P.SB = Lv.SBDef P
  hPPe : P.PPe = Lv.PPeDef P
  hXW : P.XW = XWDef P
  hPinf : P.Pinf = Lv.PinfDef P
  he : ∀ q, P.e q = Lv.eDef P q

structure FieldTie (P : MeansPack Tau ι) (Lv : Leaves Tau) (E : Type) [Field E] [NumberField E] : Prop where
  hdeg : Module.finrank ℚ E = 2 * P.f
  hdisc : Lv.dE = (NumberField.discr E).natAbs

theorem FieldTie.dE_pos {P : MeansPack Tau ι} {Lv : Leaves Tau} {E : Type} [Field E] [NumberField E]
    (h : FieldTie P Lv E) : 1 ≤ Lv.dE := by
  rw [h.hdisc]
  exact Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)

theorem sum_vdd_log {P : MeansPack Tau ι} {Lv : Leaves Tau} (t : DefTie P Lv) (hdE : 1 ≤ Lv.dE) :
    ∑ q ∈ Lv.dE.primeFactors, P.vdd q * Real.log q = Real.log P.rd := by
  rw [t.hrd]
  unfold Leaves.rdDef
  rw [Real.log_rpow (Nat.cast_pos.mpr hdE), Real.log_nat_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [t.hvdd]
  unfold Leaves.vddDef
  rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hq)]
  ring

theorem e_nonneg {P : MeansPack Tau ι} {Lv : Leaves Tau} (t : DefTie P Lv) (q : ℕ) : 0 ≤ P.e q := by
  rw [t.he]
  unfold Leaves.eDef
  exact (Finset.le_fold_max (0 : ℝ)).mpr (Or.inl le_rfl)

theorem primeSum_tied {P : MeansPack Tau ι} {Lv : Leaves Tau} (t : DefTie P Lv) :
    P.PrimeSum ↔ ∑ q ∈ Lv.SBDef P, (cppDef q + C7 * Lv.vddDef P q) * Real.log q ≤ 104 * P.L := by
  unfold MeansPack.PrimeSum
  rw [t.hSB]
  simp only [t.hcpp, t.hvdd]

theorem sixth_bound_iff_defined {P : MeansPack Tau ι} {Lv : Leaves Tau} (t : DefTie P Lv) :
    P.I6 ↔ ∑ q ∈ P.e.support, Lv.eDef P q * Real.log q ≤ Ce * P.LL0 * P.U1 + Lv.PPeDef P + XWDef P := by
  unfold MeansPack.I6
  simp only [t.he, t.hPPe, t.hXW]

def packOf (P : MeansPack Tau ι) (Lv : Leaves Tau) (e : ℕ →₀ ℝ) : MeansPack Tau ι :=
  let P1 : MeansPack Tau ι :=
    { P with
      u1 := fun τ => firstGapVector P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
      up := fun τ => upDef P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
      rd := Lv.rdDef P
      vdd := Lv.vddDef P
      cpp := cppDef
      e := e }
  let P2 : MeansPack Tau ι := { P1 with PPe := Lv.PPeDef P1, XW := XWDef P1, Pinf := Lv.PinfDef P1 }
  { P2 with SB := Lv.SBDef P2 }

theorem tie_packOf (P : MeansPack Tau ι) (Lv : Leaves Tau) (hE : ∀ q, Lv.eloc q = ∅) :
    DefTie (packOf P Lv 0) Lv := by
  refine ⟨fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
  show (0 : ℕ →₀ ℝ) q = Leaves.eDef Lv _ q
  simp [Leaves.eDef, hE]

def basePack : MeansPack (Fin 1) (Fin 1) where
  N := 1
  f := 1
  T := 0
  D := 0
  jp := 0
  m := 1
  nc := 0
  u := 0
  u1 := 0
  up := 0
  c0 := 0
  b := Real.exp 4
  rd := 1
  x := Real.exp (Real.exp 1)
  Lp := 0
  h0 := 32
  fourthRootConstant := 0
  sl := 0
  e := 0
  SB := ∅
  cpp := 0
  vdd := 0
  Pinf := 0
  PPe := 0
  XW := 0

def baseLeaves : Leaves (Fin 1) where
  dE := 1
  level := 1
  q1 := 1
  d := 1
  g1 := 1
  g2 := 1
  rr := 1
  rr' := 1
  r0 := 1
  P0 := 0
  logmu := 0
  cubicPeriodConstant := 0
  c1 := 0
  Nc := 1
  bigp := fun _ => 1
  A := 0
  eloc := fun _ => ∅

theorem tie_and_rows : DefTie (packOf basePack baseLeaves 0) baseLeaves ∧ Rows (packOf basePack baseLeaves 0) := by
  refine ⟨tie_packOf _ _ (fun _ => rfl), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) < Real.exp 4
    exact Real.exp_pos 4
  · show (1 : ℝ) ≤ Real.log (Real.exp 4)
    rw [Real.log_exp]; norm_num
  · show (1 : ℝ) ≤ Leaves.rdDef baseLeaves basePack
    simp [Leaves.rdDef, baseLeaves]
  · show (1 : ℝ) ≤ Real.exp (Real.exp 1)
    exact Real.one_le_exp (Real.exp_pos 1).le
  · show (1 : ℝ) ≤ Real.log (Real.log (Real.exp (Real.exp 1)))
    rw [Real.log_exp, Real.log_exp]
  · show (1 : ℕ) ≤ 1
    exact le_rfl
  · show (1 : ℕ) ≤ 1
    exact le_rfl
  · show 32 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) ^ 2 ≤ 32
    norm_num
  · show 4 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) ^ 2 ≤ Real.exp 4
    have := Real.add_one_le_exp 4
    norm_num at this ⊢
    linarith

theorem kap_anchor (N p A j : ℕ) (hA : A < N) (hp : p = A + 1 + j) :
    kap N p ⟨A, hA⟩ = (N : ℝ) - 1 - 2 * j := by
  unfold kap
  dsimp only
  rw [if_pos (by omega)]
  subst hp
  push_cast
  ring

theorem example_base_first_bound_eq_zero : (packOf basePack baseLeaves 0).U1 = 0 := by
  simp [MeansPack.U1, MeansPack.nrm, packOf, basePack, baseLeaves, firstGapVector, anchored]

theorem example_base_height_eq_four : (packOf basePack baseLeaves 0).B0 = 4 := by
  simp [MeansPack.B0, MeansPack.H, packOf, basePack]

theorem base_SB : Leaves.SBDef baseLeaves (packOf basePack baseLeaves 0) = {2, 3} := by
  unfold Leaves.SBDef
  rw [example_base_height_eq_four]
  simp only [baseLeaves]
  have h4 : ⌊(4 : ℝ)⌋₊ = 4 := by simp
  have h2 : (2 * 1 * 1 : ℕ).primeFactors = {2} := by simp [Nat.prime_two.primeFactors]
  rw [h4, h2]
  decide

theorem base_inputs :
    DefTie (packOf basePack baseLeaves 0) baseLeaves ∧ Rows (packOf basePack baseLeaves 0) ∧
      (packOf basePack baseLeaves 0).PrimeSum ∧ (packOf basePack baseLeaves 0).I6 := by
  refine ⟨tie_and_rows.1, tie_and_rows.2, ?_, ?_⟩
  · rw [primeSum_tied tie_and_rows.1, base_SB]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    have hL : (packOf basePack baseLeaves 0).L = 4 := by
      show Real.log (Real.exp 4) = 4
      exact Real.log_exp 4
    have l2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have l3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    rw [hL]
    simp [cppDef, Leaves.vddDef, baseLeaves, C7]
    norm_num
    nlinarith
  · unfold MeansPack.I6
    have he : (packOf basePack baseLeaves 0).e = 0 := rfl
    rw [he, example_base_first_bound_eq_zero]
    simp only [Finsupp.support_zero, Finset.sum_empty, mul_zero, zero_add]
    show (0 : ℝ) ≤ Leaves.PPeDef baseLeaves _ + XWDef _
    simp [Leaves.PPeDef, XWDef, Leaves.rdDef, baseLeaves, basePack, MeansPack.L]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

end IxMeans.MeansTie
