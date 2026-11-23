import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip

section Int

variable {E : Type*} [Field E] [NumberField E] [StarRing E]
variable {α β γ : Type*} [Fintype β]

theorem isInt_intCast (z : ℤ) : IsIntegral ℤ (z : E) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E z))

theorem isInt_natCast (d : ℕ) : IsIntegral ℤ (d : E) := by
  simpa using isInt_intCast (E := E) (d : ℤ)

def IntDiv (c : ℕ) (M : Matrix α β E) : Prop := ∃ A : Matrix α β E, (∀ i j, IsIntegral ℤ (A i j)) ∧ M = (c : E) • A

theorem intDiv_zero (c : ℕ) : IntDiv c (0 : Matrix α β E) := by
  exact ⟨0, fun _ _ => isIntegral_zero, by simp⟩

theorem intDiv_add {c : ℕ} {M N : Matrix α β E} (hM : IntDiv c M) (hN : IntDiv c N) : IntDiv c (M + N) := by
  obtain ⟨A, hA, rfl⟩ := hM
  obtain ⟨B, hB, rfl⟩ := hN
  refine ⟨A + B, fun i j => ?_, by rw [smul_add]⟩
  rw [Matrix.add_apply]
  exact (hA i j).add (hB i j)

theorem intDiv_neg {c : ℕ} {M : Matrix α β E} (hM : IntDiv c M) : IntDiv c (-M) := by
  obtain ⟨A, hA, rfl⟩ := hM
  refine ⟨-A, fun i j => ?_, by rw [smul_neg]⟩
  rw [Matrix.neg_apply]
  exact (hA i j).neg

theorem intDiv_sub {c : ℕ} {M N : Matrix α β E} (hM : IntDiv c M) (hN : IntDiv c N) : IntDiv c (M - N) := by
  rw [sub_eq_add_neg]
  exact intDiv_add hM (intDiv_neg hN)

theorem intDiv_mul {c d : ℕ} {M : Matrix α β E} {N : Matrix β γ E} (hM : IntDiv c M) (hN : IntDiv d N) :
    IntDiv (c * d) (M * N) := by
  obtain ⟨A, hA, rfl⟩ := hM
  obtain ⟨B, hB, rfl⟩ := hN
  refine ⟨A * B, fun i k => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact Finset.sum_induction _ (IsIntegral ℤ) (fun _ _ ha hb => ha.add hb) isIntegral_zero
      (fun j _ => (hA i j).mul (hB j k))
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul]

theorem intDiv_dvd {c d : ℕ} {M : Matrix α β E} (hM : IntDiv (c * d) M) : IntDiv c M := by
  obtain ⟨A, hA, rfl⟩ := hM
  refine ⟨(d : E) • A, fun i j => ?_, by rw [smul_smul, ← Nat.cast_mul]⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isInt_natCast d).mul (hA i j)

theorem intDiv_smul_nat {c : ℕ} (d : ℕ) {M : Matrix α β E} (hM : IntDiv c M) : IntDiv (d * c) ((d : E) • M) := by
  obtain ⟨A, hA, rfl⟩ := hM
  exact ⟨A, hA, by rw [smul_smul, Nat.cast_mul]⟩

theorem intDiv_one_one [DecidableEq α] [Fintype α] : IntDiv 1 (1 : Matrix α α E) := by
  refine ⟨1, fun i j => ?_, by simp⟩
  rw [Matrix.one_apply]
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

theorem intDiv_conjTranspose (hst : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (star a)) {c : ℕ} {M : Matrix α β E}
    (hM : IntDiv c M) : IntDiv c Mᴴ := by
  obtain ⟨A, hA, rfl⟩ := hM
  refine ⟨Aᴴ, fun i j => ?_, ?_⟩
  · rw [Matrix.conjTranspose_apply]
    exact hst _ (hA j i)
  · rw [Matrix.conjTranspose_smul, star_natCast]

theorem intDiv_pow [DecidableEq α] [Fintype α] {c : ℕ} {M : Matrix α α E} (hM : IntDiv c M) (j : ℕ) :
    IntDiv (c ^ j) (M ^ j) := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero]
    exact intDiv_one_one
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact intDiv_mul ih hM

theorem intDiv_sum {ι : Type*} {s : Finset ι} {c : ℕ} {M : ι → Matrix α β E} (h : ∀ i ∈ s, IntDiv c (M i)) :
    IntDiv c (∑ i ∈ s, M i) := by
  exact Finset.sum_induction _ (IntDiv c) (fun _ _ ha hb => intDiv_add ha hb) (intDiv_zero c) h

theorem exists_den [Fintype α] (hm : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * x)) (A : Matrix α β E) :
    ∃ d : ℕ, 0 < d ∧ IntDiv 1 ((d : E) • A) := by
  choose m hm0 hmi using hm
  set P : ℤ := ∏ p : α × β, m (A p.1 p.2) with hPdef
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hm0 _
  have hint : ∀ i j, IsIntegral ℤ ((P : E) * A i j) := by
    intro i j
    obtain ⟨q, hq⟩ : m (A i j) ∣ P :=
      Finset.dvd_prod_of_mem (fun p : α × β => m (A p.1 p.2)) (Finset.mem_univ (i, j))
    have e : ((m (A i j) * q : ℤ) : E) * A i j = (q : E) * ((m (A i j) : E) * A i j) := by
      push_cast; ring
    rw [hq, e]
    exact (isInt_intCast q).mul (hmi _)
  refine ⟨P.natAbs, Int.natAbs_pos.mpr hP, (P.natAbs : E) • A, fun i j => ?_, by simp⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  have hc : ((P.natAbs : ℕ) : E) = ((|P| : ℤ) : E) := by rw [Int.abs_eq_natAbs, Int.cast_natCast]
  rw [hc]
  rcases abs_choice P with h | h <;> rw [h]
  · exact hint i j
  · rw [Int.cast_neg, neg_mul]
    exact (hint i j).neg

end Int

section CayInv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]

theorem half_add_half' (M : Matrix ι ι K) : (⅟2 : K) • M + (⅟2 : K) • M = M := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem cay_eq {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) :
    cay N Z = (1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by
  have hg : geo N ((⅟2 : K) • Z) = 1 + (⅟2 : K) • Z * geo N ((⅟2 : K) • Z) := by
    have h1 := mul_neg_geom_sum ((⅟2 : K) • Z) N
    rw [hN, sub_zero, sub_mul, one_mul] at h1
    rw [add_comm]
    exact sub_eq_iff_eq_add'.mp h1
  unfold cay
  calc 1 + Z * geo N ((⅟2 : K) • Z)
      = 1 + ((⅟2 : K) • Z + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by rw [half_add_half']
    _ = (1 + (⅟2 : K) • Z * geo N ((⅟2 : K) • Z)) + (⅟2 : K) • Z * geo N ((⅟2 : K) • Z) := by
        rw [add_mul, add_assoc]
    _ = geo N ((⅟2 : K) • Z) + (⅟2 : K) • Z * geo N ((⅟2 : K) • Z) := by rw [← hg]
    _ = (1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by rw [add_mul, one_mul]

theorem cay_neg_mul {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) : cay N (-Z) * cay N Z = 1 := by
  have hN' : ((⅟2 : K) • -Z) ^ N = 0 := by rw [smul_neg, neg_pow, hN, mul_zero]
  rw [cay_eq hN', cay_eq hN, smul_neg]
  have h1 : geo N (-((⅟2 : K) • Z)) * (1 + (⅟2 : K) • Z) = 1 := by
    have := geom_sum_mul_neg (-((⅟2 : K) • Z)) N
    rw [sub_neg_eq_add, neg_pow, hN, mul_zero, sub_zero] at this
    exact this
  have h2 : (1 - (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) = 1 := by
    have := mul_neg_geom_sum ((⅟2 : K) • Z) N
    rw [hN, sub_zero] at this
    exact this
  calc (1 + -((⅟2 : K) • Z)) * geo N (-((⅟2 : K) • Z)) * ((1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z))
      = (1 - (⅟2 : K) • Z) * (geo N (-((⅟2 : K) • Z)) * (1 + (⅟2 : K) • Z)) * geo N ((⅟2 : K) • Z) := by
        rw [← sub_eq_add_neg]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h2]

end CayInv

def mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_comm_one (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]⟩, hg⟩

theorem uMat_mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) :
    uMat (mkUJ ε g hg) = g := rfl

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev N0 (D : D7) : ℕ := 2 * D.R.rS + 2

theorem lvk_lt (k : Kap X) : lvk X k < N0 D := by
  have := lvk_le X k
  unfold N0
  omega

theorem nil_of_pat {K : Type*} [CommRing K] {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) K}
    (hY : InPat (lvk X) k Y) (c : K) : (c • Y) ^ N0 D = 0 := by
  have hP := inPat_pow (inPat_smul c hY) (N0 D)
  ext i j
  have h1 := lvk_lt X j
  have h2 : N0 D ≤ k * N0 D := by
    calc N0 D = 1 * N0 D := (one_mul _).symm
      _ ≤ k * N0 D := Nat.mul_le_mul_right _ hk
  exact hP i j (Nat.lt_of_lt_of_le h1 (le_trans h2 (Nat.le_add_left _ _)))

def gE (Y : Matrix (Kap X) (Kap X) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  Bm X * cay (N0 D) Y * Bm' X

theorem gE_mul {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X (-Y) * gE X Y = 1 := by
  have hN : ((⅟2 : X.B.I.E) • Y) ^ N0 D = 0 := nil_of_pat X hk hY _
  unfold gE
  calc Bm X * cay (N0 D) (-Y) * Bm' X * (Bm X * cay (N0 D) Y * Bm' X)
      = Bm X * (cay (N0 D) (-Y) * (Bm' X * Bm X) * cay (N0 D) Y) * Bm' X := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Bm'_mul_Bm, Matrix.mul_one, cay_neg_mul hN, Matrix.mul_one, Bm_mul_Bm']

theorem gE_mul' {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X Y * gE X (-Y) = 1 := by
  have hY' : InPat (lvk X) k (-Y) := fun i j h => by rw [Matrix.neg_apply, hY i j h, neg_zero]
  have := gE_mul X hk hY'
  rw [neg_neg] at this
  exact this

theorem cT_eq (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Formalism.UG.cT (starRingEnd X.B.I.E) M = Mᴴ := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]
  rfl

theorem gE_unitary {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gE X Y)ᴴ * X.B.I.J * gE X Y = X.B.I.J := by
  have hN : ((⅟2 : X.B.I.E) • Y) ^ N0 D = 0 := nil_of_pat X hk hY _
  have hC := cay_unitary hYs hN
  rw [JB_eq] at hC
  unfold gE
  calc (Bm X * cay (N0 D) Y * Bm' X)ᴴ * X.B.I.J * (Bm X * cay (N0 D) Y * Bm' X)
      = (Bm' X)ᴴ * ((cay (N0 D) Y)ᴴ * ((Bm X)ᴴ * X.B.I.J * Bm X) * cay (N0 D) Y) * Bm' X := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bm X * Bm' X)ᴴ * X.B.I.J * (Bm X * Bm' X) := by
        rw [hC]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = X.B.I.J := by rw [Bm_mul_Bm', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def gGL {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    GL (Fin X.B.I.n) X.B.I.E :=
  ⟨gE X Y, gE X (-Y), gE_mul' X hk hY, gE_mul X hk hY⟩

theorem gGL_mem {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gGL X hk hY ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  show Formalism.UG.cT (starRingEnd X.B.I.E) (gE X Y) * X.B.I.J * gE X Y = X.B.I.J
  rw [cT_eq]
  exact gE_unitary X hk hY hYs

theorem sig_eq : (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E := by
  exact RingHom.ext fun _ => rfl

theorem gE_real (v : InfinitePlace X.B.I.F) (Y : Matrix (Kap X) (Kap X) X.B.I.E) :
    (X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v =
      Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v := by
  unfold gE Bv Bv'
  rw [Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [Matrix.mul_assoc]

theorem skew_map (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hYs : Yᴴ * JB X = -(JB X * Y)) :
    (Y.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * Y.map (X.B.I.φ v)) := by
  have hc : (Y.map (X.B.I.φ v))ᴴ = (Yᴴ).map (X.B.I.φ v) := by
    ext i j
    simp [Matrix.conjTranspose_apply, phi_star]
  have hm : (JB X).map (X.B.I.φ v) * Y.map (X.B.I.φ v) = (JB X * Y).map (X.B.I.φ v) := Matrix.map_mul.symm
  unfold JBv
  rw [hc, ← Matrix.map_mul, hYs, hm]
  ext i j
  simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]

theorem inUJ_real {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Formalism.REAL.inUJ (X.B.I.ε v) ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) := by
  rw [gE_real]
  unfold Formalism.REAL.inUJ
  have hc := cay_unitary (skew_map X v hYs) (nil_of_pat X hk (inPat_map (X.B.I.φ v) hY) (⅟2 : ℂ))
  have hh : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by rw [← conjTranspose_mul, Bv_mul_Bv', conjTranspose_one]
  calc (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)
      = (Bv' X v)ᴴ * ((cay (N0 D) (Y.map (X.B.I.φ v)))ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) *
        cay (N0 D) (Y.map (X.B.I.φ v))) * Bv' X v := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [Bv_gram, hc]
    _ = ((Bv' X v)ᴴ * (Bv X v)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [hh, Bv_mul_Bv', Matrix.one_mul, Matrix.mul_one]

def gA {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : X.B.I.GA :=
  (fun v => mkUJ (X.B.I.ε v) _ (inUJ_real X hk v hY hYs),
    Formalism.L2.SG.ColsDim.ratHom X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      ⟨gGL X hk hY, by rw [sig_eq]; exact gGL_mem X hk hY hYs⟩)

theorem gA_GF {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gA X hk hY hYs ∈ X.B.I.GFset := by
  simp only [Formalism.MainNotions.S.AutInst.GFset, Set.mem_setOf_eq]
  refine ⟨gGL X hk hY, gGL_mem X hk hY hYs, fun v => uMat_mkUJ _ _ _, ?_⟩
  rfl

theorem Mv_gA {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Mv X v (gA X hk hY hYs).1 = cay (N0 D) (Y.map (X.B.I.φ v)) := by
  have hu : uMat ((gA X hk hY hYs).1 v) = (X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v :=
    uMat_mkUJ _ _ _
  unfold Mv
  rw [hu, gE_real]
  calc Bv' X v * (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v) * Bv X v
      = (Bv' X v * Bv X v) * cay (N0 D) (Y.map (X.B.I.φ v)) * (Bv' X v * Bv X v) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Bv'_mul_Bv, Matrix.one_mul, Matrix.mul_one]

theorem gA_ninf {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gA X hk hY hYs).1 ∈ X.NinfU u := by
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.NinfU, Formalism.L2.SG.HidaSetting.Ninf, Set.mem_setOf_eq]
  intro v
  have hYv : InPat (lvk X) k (Y.map (X.B.I.φ v)) := fun i j h => by
    rw [Matrix.map_apply, hY i j h, map_zero]
  have hk' := cay_sub_one (N0 D) hYv
  apply inN_of_pat
  have hM := Mv_gA X hk v hY hYs
  unfold Mv at hM
  rw [hM]
  intro i j h
  exact hk' i j (by omega)

end RatEl

end Formalism.L2.SG.Pf.UnipB
