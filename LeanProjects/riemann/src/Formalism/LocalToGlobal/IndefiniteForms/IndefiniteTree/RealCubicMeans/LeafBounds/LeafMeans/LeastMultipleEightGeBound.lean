import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.MeansTie
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansBridge
import Development.WeilBound.SupplementaryPages.FaceFrameMatrix

noncomputable section

open Finset NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Links Formalism.IndefR.Obj

namespace IxMeans.MeansTie2

open IxMeans IxMeans.MeansTie

def nX (f r jp : ℕ) : ℕ := f * jp * (r - jp)

def zeroConstantLowerBound (f r jp : ℕ) : ℕ := max (r + (nX f r jp + 1).choose 2 + 2) (8 * f * r + 4)

def leastMultipleEightBound (f r jp : ℕ) : ℕ := 8 * ((zeroConstantLowerBound f r jp + 7) / 8)

theorem eight_dvd_least_multiple (f r jp : ℕ) : 8 ∣ leastMultipleEightBound f r jp := Dvd.intro _ rfl

theorem least_multiple_eight_ge_bound (f r jp : ℕ) : zeroConstantLowerBound f r jp ≤ leastMultipleEightBound f r jp := by
  unfold leastMultipleEightBound
  omega

theorem least_multiple_eight_le (f r jp c : ℕ) (h8 : 8 ∣ c) (hc : zeroConstantLowerBound f r jp ≤ c) : leastMultipleEightBound f r jp ≤ c := by
  obtain ⟨t, rfl⟩ := h8
  unfold leastMultipleEightBound
  omega

structure PgNums where

  Nr : ℝ

  f : ℝ

  m : ℝ

  k : ℝ

  jp : ℕ

  DY : ℝ

  T : ℝ

  b : ℝ

  x : ℝ

  rd : ℝ

  Lc : ℝ

  eta : ℝ

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def pgOf (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) : PgNums where
  Nr := (faceLiftPage R F I J hd).Nr
  f := (faceLiftPage R F I J hd).f
  m := (faceLiftPage R F I J hd).m
  k := (faceLiftPage R F I J hd).k
  jp := (faceLiftFactor R F I J hd j).q'
  DY := (faceLiftFactor R F I J hd j).DY
  T := (faceLiftFactor R F I J hd j).T
  b := (faceLiftPage R F I J hd).b
  x := (faceLiftPage R F I J hd).x
  rd := (faceLiftPage R F I J hd).rd
  Lc := (faceLiftPage R F I J hd).Lc
  eta := (faceLiftPage R F I J hd).η

theorem pgOf_ranks (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) :
    (pgOf R F I J hd j).Nr = (D.R.r : ℝ) ∧ (pgOf R F I J hd j).f = (D.R.f : ℝ) ∧
      (pgOf R F I J hd j).m = (D.R.m : ℝ) ∧ (pgOf R F I J hd j).k = (D.R.k : ℝ) ∧
      (pgOf R F I J hd j).jp = D.R.m - ((j : ℕ) + 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem pgOf_jp_le (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) : (pgOf R F I J hd j).jp ≤ D.R.r := by
  show D.R.m - ((j : ℕ) + 1) ≤ D.R.k + D.R.m - 1
  have := D.R.m_add_three_le_k
  omega

variable {Tau ι : Type} [Fintype Tau] [Fintype ι]

structure PackPage (r4 : ℝ) (P : MeansPack Tau ι) (pg : PgNums) : Prop where
  hN : (P.N : ℝ) = pg.Nr
  hf : (P.f : ℝ) = pg.f
  hm : (P.m : ℝ) = pg.m
  hjp : P.jp = pg.jp
  hD : (P.D : ℝ) = pg.DY
  hT : (P.T : ℝ) = pg.T
  hb : P.b = pg.b
  hx : P.x = pg.x
  hrd : P.rd = pg.rd
  hLp : P.Lp = pg.Lc

  hh0 : P.h0 = pg.eta / pg.m

  hc0 : P.c0 = (leastMultipleEightBound P.f P.N P.jp : ℝ)

  hnc8 : 8 ∣ P.nc
  hnc1 : 8 * P.f * P.N + 4 ≤ P.nc
  hnc2 : P.nc ≤ 16 * P.f * P.N ^ 2 + 8

  fourth_root_eq : P.fourthRootConstant = r4

structure LeafTie (P : MeansPack Tau ι) (Lv : Leaves Tau) (pg : PgNums) : Prop where

  hbigp : ∀ τ, Lv.bigp τ = P.N - P.jp

  hA : (Lv.A : ℝ) + 2 = pg.k

  heloc : ∀ q, q.Prime → (Lv.eloc q).Nonempty

  heloc0 : ∀ q, ¬ q.Prime → Lv.eloc q = ∅

  hlevel : 1 ≤ Lv.level

theorem seventh_constant_eq {r4 : ℝ} {P : MeansPack Tau ι} {pg : PgNums} (t : PackPage r4 P pg) : P.indexMeanConstant = 100 + 9 * |r4| := by
  unfold MeansPack.indexMeanConstant
  rw [t.fourth_root_eq]

theorem error_bound_eq_defined {r4 : ℝ} {P : MeansPack Tau ι} {pg : PgNums} (t : PackPage r4 P pg) :
    P.E0 = (P.f : ℝ) * P.N * ((leastMultipleEightBound P.f P.N P.jp : ℝ) + 4 * P.N) := by
  unfold MeansPack.E0
  rw [t.hc0]

theorem rnd_le_e {P : MeansPack Tau ι} {Lv : Leaves Tau} {pg : PgNums} (td : DefTie P Lv) (tl : LeafTie P Lv pg)
    (q : ℕ) (hq : q.Prime) : ∃ y ∈ Lv.eloc q, y + Lv.rnd P q ≤ P.e q := by
  obtain ⟨y, hy⟩ := tl.heloc q hq
  refine ⟨y, hy, ?_⟩
  rw [td.he]
  unfold Leaves.eDef
  exact (Finset.le_fold_max _).mpr (Or.inr ⟨y, hy, le_rfl⟩)

theorem log_scale_eq_page_value {r4 : ℝ} (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) {P : MeansPack Tau ι} (t : PackPage r4 P (pgOf R F I J hd j)) :
    (faceLiftPage R F I J hd).LL0 = P.LL0 := by
  unfold MeansPack.LL0 SlopeBoundParameters.LL0 SlopeBoundParameters.llx SlopeBoundParameters.Lc
  rw [t.hb, t.hx, t.hrd, t.hLp]
  rfl

structure RecTie6 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) (P : MeansPack Tau (J.ι j)) : Prop where
  hX : J.X j = P.X
  hsl : J.sl j = P.sl
  hU : (faceLiftFactor R F I J hd j).U = P.U
  hE : J.E0 j = P.E0
  hcc : J.cc j = P.cc
  hQ : J.Qcc j = P.Qcc

theorem recTie_of {r4 : ℝ} (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) {P : MeansPack Tau (J.ι j)} (t6 : RecTie6 R F I J hd j P)
    (tp : PackPage r4 P (pgOf R F I J hd j)) : RecTie R F I J hd j P :=
  ⟨t6.hX, t6.hsl, tp.hT.symm, log_scale_eq_page_value R F I J hd j tp, t6.hU, t6.hE, t6.hcc, t6.hQ⟩

structure FullTie (r4 : ℝ) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) (P : MeansPack Tau (J.ι j)) (Lv : Leaves Tau) : Prop where
  recs : RecTie6 R F I J hd j P
  page : PackPage r4 P (pgOf R F I J hd j)
  defs : DefTie P Lv
  leaves : LeafTie P Lv (pgOf R F I J hd j)

theorem leafMeans_of_tied (r4 : ℝ) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat)
    (J : SlopeArithmeticParameters R.toRealDat) (hd : NeZero D.host.d) (j : Fin D.R.m) (P : MeansPack Tau (J.ι j)) (Lv : Leaves Tau)
    (t : FullTie r4 R F I J hd j P Lv) (h : Rows P) (ha : P.IntermediateScaleBounds) (hdd : P.HeightGapBound) (he : P.SpreadBoundVariant) (h6 : P.I6)
    (hp : P.PrimeSum) (h7 : P.I7) {Ca Cb : ℝ} (hCa : 100 + 9 * |r4| ≤ Ca) (hCb : Ce + 105 ≤ Cb) :
    Formalism.L2.Indef.Tree.LeafMeans Ca Cb (faceLiftFactor R F I J hd j) :=
  leafMeans_of_pack R F I J hd j P (recTie_of R F I J hd j t.recs t.page) h ha hdd he h6 hp h7
    (by rw [seventh_constant_eq t.page]; exact hCa) hCb

def basePg : PgNums where
  Nr := 2
  f := 1
  m := 1
  k := 2
  jp := 0
  DY := 0
  T := 0
  b := Real.exp 4
  x := Real.exp (Real.exp 1)
  rd := 1
  Lc := 0
  eta := 128

def basePack2 : MeansPack (Fin 1) (Fin 1) where
  N := 2
  f := 1
  T := 0
  D := 0
  jp := 0
  m := 1
  nc := 24
  u := 0
  u1 := 0
  up := 0
  c0 := 24
  b := Real.exp 4
  rd := 1
  x := Real.exp (Real.exp 1)
  Lp := 0
  h0 := 128
  fourthRootConstant := 0
  sl := 0
  e := 0
  SB := ∅
  cpp := 0
  vdd := 0
  Pinf := 0
  PPe := 0
  XW := 0

def baseLeaves2 : Leaves (Fin 1) where
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
  bigp := fun _ => 2
  A := 0
  eloc := fun q => if q.Prime then {0} else ∅

def baseE : ℕ →₀ ℝ := Finsupp.single 2 2

def tiedPack : MeansPack (Fin 1) (Fin 1) := packOf basePack2 baseLeaves2 baseE

theorem tiedPack_vdd (q : ℕ) : tiedPack.vdd q = 0 := by
  show Leaves.vddDef baseLeaves2 basePack2 q = 0
  simp [Leaves.vddDef, baseLeaves2]

theorem tiedPack_rnd (q : ℕ) : Leaves.rnd baseLeaves2 tiedPack q = if q ∣ 2 then 2 else 0 := by
  unfold Leaves.rnd kpDef
  rw [tiedPack_vdd]
  simp only [baseLeaves2, mul_one]
  split_ifs <;> norm_num

theorem tie_tiedPack : DefTie tiedPack baseLeaves2 := by
  refine ⟨fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
  show baseE q = Leaves.eDef baseLeaves2 tiedPack q
  unfold Leaves.eDef
  rw [tiedPack_rnd]
  by_cases hq : q.Prime
  · have hel : baseLeaves2.eloc q = {0} := if_pos hq
    rw [hel, Finset.fold_singleton]
    by_cases h2 : q = 2
    · subst h2
      simp [baseE]
    · have hn : ¬ q ∣ 2 := by
        intro hd
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
        · exact hq.one_lt.ne' h
        · exact h2 h
      rw [if_neg hn]
      simp [baseE, Ne.symm h2]
  · have hel : baseLeaves2.eloc q = ∅ := if_neg hq
    rw [hel, Finset.fold_empty]
    have h2 : q ≠ 2 := fun h => hq (h ▸ Nat.prime_two)
    simp [baseE, Ne.symm h2]

theorem least_multiple_eight_base_eq : leastMultipleEightBound 1 2 0 = 24 := by decide

theorem page_tiedPack : PackPage 0 tiedPack basePg := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · show ((2 : ℕ) : ℝ) = 2; norm_num
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show Leaves.rdDef baseLeaves2 basePack2 = 1
    simp [Leaves.rdDef, baseLeaves2]
  · show (128 : ℝ) = 128 / 1; norm_num
  · show (24 : ℝ) = ((leastMultipleEightBound 1 2 0 : ℕ) : ℝ)
    rw [least_multiple_eight_base_eq]; norm_num
  · show 8 ∣ 24; decide
  · show 8 * 1 * 2 + 4 ≤ 24; decide
  · show 24 ≤ 16 * 1 * 2 ^ 2 + 8; decide

theorem leaf_tiedPack : LeafTie tiedPack baseLeaves2 basePg := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, le_rfl⟩
  · show ((0 : ℕ) : ℝ) + 2 = 2; norm_num
  · intro q hq
    show (if q.Prime then ({0} : Finset ℝ) else ∅).Nonempty
    rw [if_pos hq]; exact Finset.singleton_nonempty 0
  · intro q hq
    show (if q.Prime then ({0} : Finset ℝ) else ∅) = ∅
    rw [if_neg hq]

theorem rows_tiedPack : Rows tiedPack := by
  have e2 : (5 : ℝ) ≤ Real.exp 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h; linarith
  have e4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) < Real.exp 4
    exact Real.exp_pos 4
  · show (1 : ℝ) ≤ Real.log (Real.exp 4)
    rw [Real.log_exp]; norm_num
  · show (1 : ℝ) ≤ Leaves.rdDef baseLeaves2 basePack2
    simp [Leaves.rdDef, baseLeaves2]
  · show (1 : ℝ) ≤ Real.exp (Real.exp 1)
    exact Real.one_le_exp (Real.exp_pos 1).le
  · show (1 : ℝ) ≤ Real.log (Real.log (Real.exp (Real.exp 1)))
    rw [Real.log_exp, Real.log_exp]
  · show (1 : ℕ) ≤ 1
    exact le_rfl
  · show (1 : ℕ) ≤ 2
    norm_num
  · show 32 * ((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ 2 ≤ 128
    norm_num
  · show 4 * ((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ 2 ≤ Real.exp 4
    rw [e4]; norm_num; nlinarith

theorem ties_and_rows :
    DefTie tiedPack baseLeaves2 ∧ PackPage 0 tiedPack basePg ∧ LeafTie tiedPack baseLeaves2 basePg ∧ Rows tiedPack :=
  ⟨tie_tiedPack, page_tiedPack, leaf_tiedPack, rows_tiedPack⟩

end IxMeans.MeansTie2
