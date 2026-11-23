import Mathlib
import Formalism.LocalToGlobal.Divisibility.Inputs
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.IndefiniteForms.QuadraticExampleRankThreePackage
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import Formalism.DivisorInequality.BaseLevelBoundsWithCovolume
import Formalism.DivisorInequality.DivisorInequalityProofs.EvenDegreeWeightBounds
import Formalism.BranchSandwichDivisors.ChainDenominatorCoupled
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.PerEmbeddingCoupledBound
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open Formalism.LatticeIndexTer (ph)

section Numbers

variable {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl)

namespace RecNums

theorem x_pos : 0 < R.x := lt_trans zero_lt_one R.p1
theorem L_nonneg : 0 ≤ R.L := by
  rw [R.p3]
  exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one R.p1)) _
theorem b_ge : 1 ≤ R.b := by
  rw [R.p4]
  exact Real.one_le_exp R.L_nonneg
theorem a_ge : 1 ≤ R.a := by
  have h1 := R.p1
  have h2 := R.b_ge
  rw [R.p5]
  nlinarith
theorem La_nonneg : 0 ≤ R.La := by
  have h1 := R.a_ge
  have h2 := R.p6
  rw [R.p9]
  exact Real.log_nonneg (by nlinarith)
theorem Nn_ge : 1 ≤ R.Nn := by
  linarith [R.p1, R.p2, R.p6, R.p11, R.p14, R.p15, R.p16, R.p17, R.p18, R.p19, R.p20, R.p24, R.p25, R.p26, R.p27, R.p28,
    R.p29, R.p30, R.p31, R.p32, R.p33, R.p34, R.p35, R.p36, R.p37, R.p38, R.c1, R.c3, R.c4, R.c5]
theorem L_ge : 1 ≤ R.L := by
  rw [R.p3]
  exact Real.one_le_rpow (le_of_lt R.p1) (le_of_lt R.p2)

theorem La_eq : R.La = Real.log R.x + R.L + Real.log R.rd := by
  have hx : 0 < R.x := R.x_pos
  have hb : 0 < R.b := by rw [R.p4]; exact Real.exp_pos _
  have hrd : 0 < R.rd := by linarith [R.p6]
  rw [R.p9, R.p5, Real.log_mul (mul_pos hx hb).ne' hrd.ne', Real.log_mul hx.ne' hb.ne', R.p4, Real.log_exp]

theorem L_le_La : R.L ≤ R.La := by
  rw [R.La_eq]
  have h1 := Real.log_nonneg (le_of_lt R.p1)
  have h2 := Real.log_nonneg R.p6
  linarith

theorem log2a : 0 ≤ Real.log (2 * R.a) ∧ Real.log (2 * R.a) ≤ 2 * R.La := by
  have ha := R.a_ge
  have hx : 0 < R.x := R.x_pos
  have hb : 0 < R.b := by rw [R.p4]; exact Real.exp_pos _
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have e1 : Real.log (2 * R.a) = Real.log 2 + (Real.log R.x + R.L) := by
    rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < R.a).ne', R.p5, Real.log_mul hx.ne' hb.ne', R.p4, Real.log_exp]
  rw [e1, R.La_eq]
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h3 := Real.log_nonneg (le_of_lt R.p1)
  have h4 := Real.log_nonneg R.p6
  have h5 := R.L_ge
  linarith

theorem unit_nonneg : 0 ≤ R.x ^ R.eps * (R.B0 + R.Nc) := by
  have hx : 0 ≤ R.x := le_of_lt R.x_pos
  have hf : 0 ≤ R.f := le_trans (Nat.cast_nonneg _) R.p13
  have hb : 0 ≤ R.b := by linarith [R.b_ge]
  have hm : 0 ≤ R.m := by linarith [R.p14]
  have hxe := Real.rpow_nonneg hx R.eps
  apply mul_nonneg hxe
  rw [R.p10]
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf hm) hb) hxe) R.p11

theorem hu_eq : R.hu = R.hA + ∑ j, R.hB j - ∑ j, R.hX j := by
  show R.hA + ∑ j, (R.hB j - R.hX j) = _
  rw [Finset.sum_sub_distrib]
  ring

def NcF : ℝ := R.x ^ R.eps * R.Nc / (Real.log R.x) ^ 2

theorem NcF_nonneg : 0 ≤ R.NcF := by
  show 0 ≤ R.x ^ R.eps * R.Nc / (Real.log R.x) ^ 2
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt R.x_pos) _) R.p11) (sq_nonneg _)

theorem NcF_spec : (Real.log R.x) ^ 2 * R.NcF = R.x ^ R.eps * R.Nc := by
  show (Real.log R.x) ^ 2 * (R.x ^ R.eps * R.Nc / (Real.log R.x) ^ 2) = R.x ^ R.eps * R.Nc
  have hl : Real.log R.x ≠ 0 := (Real.log_pos R.p1).ne'
  field_simp

end RecNums

theorem HtNums.le_hu {R : RecNums J Pl} {Emb : Type} [Fintype Emb] [Nonempty Emb] (H : HtNums R Emb) (mlam : ℝ)
    (hm : ∑ j, R.hX j ≤ mlam) :
    H.hPn + ∑ j, (∑ s, H.sz j s) / (Fintype.card Emb : ℝ) - mlam ≤ R.hu :=
  Formalism.DivisorInequality.height_bound_at_set J Pl Emb R.TT R.r R.hu H.hPn mlam R.logT (fun j => (∑ s, H.sz j s) / (Fintype.card Emb : ℝ))
    R.aT R.logH R.Ch R.nV R.Lp R.ν R.x R.eps R.L R.b R.a R.rd R.La R.m R.f R.k R.Nn R.S R.η R.b' R.logOm
    H.g0 H.sz H.MainNotions H.logOmτ H.logth0 H.logh H.logh' H.vv H.logg H.C2 H.Cth H.C4 H.c5 H.c6 H.CT H.C8 H.Ce
    H.ev H.bT H.nτ H.lam1 H.D0 H.D1 H.logc H.logxi H.Cev
    rfl hm (fun _ _ => le_refl _) (fun _ => rfl) H.i1 H.i2 H.i3 H.i4 H.i5 H.i6 H.i7 H.i8 H.i9
    H.i10.1 H.i10.2.1 H.i10.2.2.1 H.i10.2.2.2.1 H.i10.2.2.2.2.1 H.i10.2.2.2.2.2.1 H.i10.2.2.2.2.2.2
    H.t1 H.t2 H.t3 H.t4 H.t5 H.t6 H.t7 H.t8 H.t9 H.t10.1 H.t10.2.1 H.t10.2.2 R.p34 H.t11.1 H.t11.2
    R.p1.le R.p2 R.p3 R.p4 R.p5 R.p6 R.p9 R.p13 R.p14 R.p15 R.p16 R.p17 R.p18 R.p20 H.k1 H.k2 H.k3

theorem HtNums.hPn_le_hA {R : RecNums J Pl} {Emb : Type} [Fintype Emb] (H : HtNums R Emb) : H.hPn ≤ R.hA :=
  Formalism.BranchingDeterminantCap.stepDiiiRecord Pl R.TT H.hPn R.logT H.ev R.aT H.bT H.nτ H.lam1 H.D0 H.D1 H.logc H.logxi
    R.a R.La R.L R.m R.f R.k R.Nn R.S R.η R.b' H.CT H.Cev R.Ch H.t1 H.t2 H.t3 H.t4 H.t5 H.t6 H.t7 H.t8 H.t9
    H.t10.1 H.t10.2.1 H.t10.2.2 R.L_le_La R.La_nonneg R.log2a.1 R.log2a.2 R.p14 (by linarith [R.p17, R.p16])
    (by linarith [R.p16]) R.p18 R.p20 R.p34 R.p13 H.t11.1 H.t11.2 H.k1

theorem RecNums.divIneq (muC mu0 Fo Lpass Eb : ℝ) (hC : muC ≤ mu0 + Lpass)
    (hM : mu0 ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + 2 * Fo + Eb)
    (hpass : Lpass ≤ 1 + R.C0 * (R.m * R.lam0)) (hEb : Eb ≤ R.errB) :
    muC + R.hu - 2 * Fo ≤ R.rhs := by
  have hf : 0 ≤ R.f := by linarith [R.p15]
  have hm : 0 ≤ R.m := by linarith [R.p14]
  have hN : 0 ≤ R.Nn := by linarith [R.Nn_ge]
  have hL := R.L_nonneg
  have hLa := R.La_nonneg
  have hη := R.p20
  have hS := R.p18
  have hb' := R.p34
  have hC0 : 0 ≤ R.C0 := by linarith [R.c1]
  have H := Formalism.DivisionValues.divIneqRecord J Pl R.TT muC mu0 Fo R.hu R.hA (∑ j, R.hX j) R.logT
    R.hB R.aT (fun j ρ => ∑ i, ph (R.ν j ρ i)) (fun j ρ => ∑ i, R.ν j ρ i) R.logH R.x R.eps R.L R.b R.a R.rd R.La R.B0 R.NcF
    R.m R.f R.k R.Nn R.S R.tt R.η R.w'' R.b' R.lam0 R.C0 R.ce Lpass Eb
    (R.m * (R.Ch * R.f * R.nV ^ 2 * R.Lp))
    (R.Ch * ((R.TT.card : ℝ) * R.b' * R.Nn + R.f * (R.m * R.η + R.S) * R.Nn + R.f * R.Nn ^ 2) * R.La)
    R.logOm (fun _ => R.Ch * R.f * R.Nn ^ 2 * (R.La + R.m ^ 3 * R.L)) R.pq R.w R.eE R.δ
    hC hM R.hu_eq (fun _ => le_refl _)
    (by
      simp only [RecNums.hX, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12]
      exact le_refl _)
    (le_refl _) R.weight_height_sum_le R.weight_sum_eq R.p1.le R.p2 R.p3 R.p4 R.p5 R.p6 R.p7 R.p8 R.p9 R.p10 R.NcF_nonneg
    R.p12 R.p13 R.p14 R.p15 R.p16 R.Nn_ge R.p18 R.p19 R.p20 R.p21 R.p22 R.p23 R.p24 R.p25 R.p26 R.p27 R.p28 R.p29
    R.p30 R.p31 R.p32 R.p33 R.c1 R.c2 hpass
    (by rw [R.NcF_spec]; have := hEb; unfold RecNums.errB at this; linarith)
    (fun _ => by
      have hX : 0 ≤ R.f * R.Nn ^ 2 * R.La + R.f * R.m ^ 3 * R.Nn ^ 2 * R.L := by positivity
      calc R.Ch * R.f * R.Nn ^ 2 * (R.La + R.m ^ 3 * R.L)
          = R.Ch * (R.f * R.Nn ^ 2 * R.La + R.f * R.m ^ 3 * R.Nn ^ 2 * R.L) := by ring
        _ ≤ R.C0 * (R.f * R.Nn ^ 2 * R.La + R.f * R.m ^ 3 * R.Nn ^ 2 * R.L) := mul_le_mul_of_nonneg_right R.c4 hX)
    (by
      have h1 : R.nV ^ 2 ≤ R.Nn ^ 2 := pow_le_pow_left₀ R.p36 R.p37 2
      have h2 : 0 ≤ R.Ch * R.Lp := mul_nonneg R.c3 R.p38
      have h3 : R.nV ^ 2 * (R.Ch * R.Lp) ≤ R.Nn ^ 2 * (R.C0 * R.La) :=
        mul_le_mul h1 R.c5 h2 (by positivity)
      have h4 : 0 ≤ R.m * R.f := mul_nonneg hm hf
      calc R.m * (R.Ch * R.f * R.nV ^ 2 * R.Lp) = R.m * R.f * (R.nV ^ 2 * (R.Ch * R.Lp)) := by ring
        _ ≤ R.m * R.f * (R.Nn ^ 2 * (R.C0 * R.La)) := mul_le_mul_of_nonneg_left h3 h4
        _ = R.C0 * R.m * R.f * R.Nn ^ 2 * R.La := by ring)
    (by
      have hY : 0 ≤ (R.TT.card : ℝ) * R.b' * R.Nn + R.f * (R.m * R.η + R.S) * R.Nn + R.f * R.Nn ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right R.c4 hY) hLa)
    R.sE R.sδ
  rw [R.NcF_spec] at H
  unfold RecNums.rhs
  have e : R.x ^ R.eps * R.B0 + R.x ^ R.eps * R.Nc = R.x ^ R.eps * (R.B0 + R.Nc) := by ring
  rw [e] at H
  exact H

theorem le_exp_half {t h : ℝ} (H : t ^ 2 ≤ Real.exp h) : t ≤ Real.exp (h / 2) := by
  have he : Real.exp (h / 2) ^ 2 = Real.exp h := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  by_contra hc
  push_neg at hc
  have hp := Real.exp_pos (h / 2)
  nlinarith

theorem log_exp_half_sq (h : ℝ) : Real.log (Real.exp (h / 2) ^ 2) = h := by
  rw [sq, ← Real.exp_add, Real.log_exp]
  ring

theorem passage_sizes {de f r g Q : ℝ} (hde : de = 8 * f * r / g) (hf : 0 ≤ f) (hr : 0 ≤ r) (hg : 0 < g) (hQ : 1 ≤ Q)
    (hgQ : 24 * f * r * Q ≤ g) : 0 ≤ de ∧ de ≤ 1 / 3 ∧ 3 * de * Q ≤ 1 := by
  subst hde
  have hfr : 0 ≤ f * r := mul_nonneg hf hr
  have hq : 24 * f * r * 1 ≤ 24 * f * r * Q := mul_le_mul_of_nonneg_left hQ (by nlinarith)
  refine ⟨div_nonneg (by nlinarith) hg.le, ?_, ?_⟩
  · rw [div_le_iff₀ hg]
    nlinarith
  · rw [show 3 * (8 * f * r / g) * Q = 24 * f * r * Q / g by ring, div_le_one hg]
    exact hgQ

end Numbers

theorem complex_height_cast (hH : HeightBoundConstant) {K : Type} [Field K] [NumberField K] [StarRing K] {a n dQ D m : ℕ}
    (c : Fin (m + 1) → ℕ) (c0 : c 0 = a) (hd : dQ = D)
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (hXc : ∀ i v, IsUnit (Xc i v).det)
    (hXz : ∀ v i j, Xc 0 v i j = Xa v (Fin.cast c0 i) (Fin.cast c0 j))
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin dQ) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin dQ) (Fin dQ) ℂ) (hXQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin dQ) K) (hι : Function.Bijective ι.mulVec)
    (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin dQ → K)) (hQp : (⨆ p, Qp p) = ⊤)
    (κ : InfinitePlace K → ℝ) (lam : J → Ix → InfinitePlace K → ℝ) (hκ : ∀ v, 0 < κ v) (hlam : ∀ j p v, 0 < lam j p v)
    (hsc : ∀ v p, IsScalarOn XQ XE v ι (Qp p) (κ v * ∏ j, lam j p v))
    (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec fun i => φ (Fin.cast c0 i)) F)
    (hne : B ≠ 0) (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v)
    (hkU : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) :
    Formalism.HN.htMap (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) B ≤
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2)) -
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (lam j p v)) - meanLog κ := by
  subst c0 hd
  obtain rfl : Xc 0 = Xa := by
    funext v; ext i j; simpa using hXz v i j
  exact (hH K n dQ m c Xc hXc Kj H X0 hX0 P hP XQ hXQ XE hXE ι (isUnit_det_of_bij _ hι) Ix J Qp hQp κ lam lam hκ hlam
    (fun _ _ _ => le_rfl) hsc Pt B (by simpa using hB) hne pU kU hpU hkU).2

section KerChainDefs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def famIpAt (F : Formalism.L2.Col.GFam K) (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) : ℂ :=
  ∑ b, (F.mem b).ipAt (h b) v (φ b : (F.mem b).D → F.V) (ψ b : (F.mem b).D → F.V)

structure KerChain (K : Type) [Field K] [NumberField K] [StarRing K] where

  n : ℕ

  F : ℕ → Formalism.L2.Col.GFam K

  hF : ∀ j, (F j).Ok

  kk : Formalism.L2.Col.KerFam F

  S : Formalism.L2.Col.GSD K

  hS : S.Ok

  S₁ : Formalism.L2.Col.GSD K

  hS₁ : S₁.Ok

  Y : Formalism.L2.Col.Cpl S

  cp : ∀ b : (F n).β, Formalism.L2.Col.CplKer ((F n).mem b) S S₁ Y

namespace KerChain

variable (Q : KerChain K)

def col : (Q.F 0).Forms →ₗ[K] Q.S₁.EqFun := Formalism.L2.Col.colCpl Q.kk Q.hF Q.n Q.cp Q.hS

def step (j : ℕ) : (Q.F j).Forms →ₗ[K] (Q.F (j + 1)).Forms := Q.kk.step Q.hF j

def cpl : (Q.F Q.n).Forms →ₗ[K] Q.S₁.EqFun :=
  (∑ b : (Q.F Q.n).β, (((Q.cp b).comp Q.hS Q.S.outSec).opOf (Q.hF Q.n b) ((Q.F Q.n).mem b).outSec) ∘ₗ (LinearMap.proj b))

theorem col_eq : Q.col = Q.cpl ∘ₗ Q.kk.colTo Q.hF Q.n := rfl

end KerChain

end KerChainDefs

section OfCol

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu))
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def KerChain.ofCol {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K where
  n := m2
  F := chF W sel mu L u
  hF := hF
  kk := A.kk
  S := midGSD W sel mu L u m2 b
  hS := hF (m2 + 1) b
  S₁ := evGSD W Ch sel mu P u
  hS₁ := hE
  Y := ybCpl W sel mu cst L u m2 b hY
  cp := A.cp

theorem KerChain.ofCol_col {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) :
    (KerChain.ofCol W Ch sel mu cst L A hF hE).col = A.colF hF := rfl

end OfCol

section Comparison₂

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

structure ChainTie {Df : DefSide Bs} {Dc : DefCols Df} {u : Dc.Mem} (ch : ColChain Dc u) (Q : KerChain K) where

  hmm : ch.mm = Q.n + 1

  coF : ∀ i (h : i ≤ Q.n), (Fin (ch.c ⟨i, by omega⟩) → K) →ₗ[K] (Q.F i).Forms

  coL : (Fin (ch.c ⟨Q.n + 1, by omega⟩) → K) →ₗ[K] Q.S₁.EqFun

  metF : ∀ i (h : i ≤ Q.n) (v : InfinitePlace K) (x : Fin (ch.c ⟨i, by omega⟩) → K),
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨i, by omega⟩))) (ch.X ⟨i, by omega⟩) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F i) (Q.hF i) v (coF i h x) (coF i h x)

  metL : ∀ (v : InfinitePlace K) (x : Fin (ch.c ⟨Q.n + 1, by omega⟩) → K),
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨Q.n + 1, by omega⟩))) (ch.X ⟨Q.n + 1, by omega⟩) v x ^ 2 : ℝ) : ℂ) =
      Q.S₁.ipAt Q.hS₁ v (coL x) (coL x)

  kerF : ∀ j (h : j < Q.n) (x : Fin (ch.c ⟨j, by omega⟩) → K),
    coF (j + 1) h ((ch.Kj ⟨j, by omega⟩).mulVec x) = Q.step j (coF j h.le x)

  kerC : ∀ x : Fin (ch.c ⟨Q.n, by omega⟩) → K, coL ((ch.Kj ⟨Q.n, by omega⟩).mulVec x) = Q.cpl (coF Q.n le_rfl x)

variable {Df : DefSide Bs} {Dc : DefCols Df} {u : Dc.Mem} {ch : ColChain Dc u} {Q : KerChain K}

theorem ChainTie.chain_le (T : ChainTie ch Q) : ∀ i (h : i ≤ Q.n) (x : Fin (ch.c 0) → K),
    T.coF i h ((chainMat ch.Kj ⟨i, by have := T.hmm; omega⟩).mulVec x) = Q.kk.colTo Q.hF i (T.coF 0 (Nat.zero_le _) x)
  | 0, h, x => by
    have h0 := (chainSpec.2 K ch.mm ch.c ch.Kj).1
    show T.coF 0 h ((chainMat ch.Kj 0).mulVec x) = T.coF 0 (Nat.zero_le _) x
    rw [h0, Matrix.one_mulVec]
  | i + 1, h, x => by
    have hi : i < ch.mm := by have := T.hmm; omega
    have h1 := (chainSpec.2 K ch.mm ch.c ch.Kj).2 ⟨i, hi⟩
    have ih := ChainTie.chain_le T i (by omega) x
    show T.coF (i + 1) h ((chainMat ch.Kj (Fin.succ ⟨i, hi⟩)).mulVec x) = Q.step i (Q.kk.colTo Q.hF i (T.coF 0 (Nat.zero_le _) x))
    rw [h1, ← Matrix.mulVec_mulVec, ← ih]
    exact T.kerF i h _

theorem ChainTie.chain (T : ChainTie ch Q) (x : Fin (ch.c 0) → K) :
    T.coL ((chainMat ch.Kj ⟨Q.n + 1, by have := T.hmm; omega⟩).mulVec x) = Q.col (T.coF 0 (Nat.zero_le _) x) := by
  have e : (chainMat ch.Kj ⟨Q.n + 1, by have := T.hmm; omega⟩).mulVec x =
      (ch.Kj ⟨Q.n, by have := T.hmm; omega⟩).mulVec ((chainMat ch.Kj ⟨Q.n, by have := T.hmm; omega⟩).mulVec x) :=
    (Matrix.mulVec_mulVec _ _ _).symm
  rw [e, T.kerC, T.chain_le Q.n le_rfl x]
  rfl

theorem ChainTie.step_norm (T : ChainTie ch Q) (j : ℕ) (h : j < Q.n) (v : InfinitePlace K) (x : Fin (ch.c ⟨j, by have := T.hmm; omega⟩) → K) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨j + 1, by have := T.hmm; omega⟩))) (ch.X ⟨j + 1, by have := T.hmm; omega⟩) v
        ((ch.Kj ⟨j, by have := T.hmm; omega⟩).mulVec x) ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F (j + 1)) (Q.hF (j + 1)) v (Q.step j (T.coF j h.le x)) (Q.step j (T.coF j h.le x)) := by
  rw [T.metF (j + 1) h v, T.kerF j h x]

theorem ChainTie.cpl_norm (T : ChainTie ch Q) (v : InfinitePlace K) (x : Fin (ch.c ⟨Q.n, by have := T.hmm; omega⟩) → K) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨Q.n + 1, by have := T.hmm; omega⟩))) (ch.X ⟨Q.n + 1, by have := T.hmm; omega⟩) v
        ((ch.Kj ⟨Q.n, by have := T.hmm; omega⟩).mulVec x) ^ 2 : ℝ) : ℂ) =
      Q.S₁.ipAt Q.hS₁ v (Q.cpl (T.coF Q.n le_rfl x)) (Q.cpl (T.coF Q.n le_rfl x)) := by
  rw [T.metL v, T.kerC x]

def ChainTie.First (T : ChainTie ch Q) (f : (Fin (ch.c 0) → K) →ₗ[K] (Q.F 0).Forms) : Prop :=
  ∀ x, T.coF 0 (Nat.zero_le _) x = f x

theorem ChainTie.last_eq (T : ChainTie ch Q) :
    (Fin.last ch.mm : Fin (ch.mm + 1)) = ⟨Q.n + 1, by have := T.hmm; omega⟩ := Fin.ext (by rw [Fin.val_last]; exact T.hmm)

def ChainTie.Last (T : ChainTie ch Q) (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) : Prop :=
  ∀ (y : Fin (ch.c ⟨Q.n + 1, by have := T.hmm; omega⟩) → K) (F : Fin (Df.nV Bs.μ0) → K),
    ch.PtL (fun l => y (Fin.cast (congrArg ch.c T.last_eq) l)) F = g (T.coL y) F

omit [NumberField K] [StarRing K] in

theorem chainMat_mulVec_cast {m : ℕ} {c : Fin (m + 1) → ℕ} (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (i j : Fin (m + 1)) (h : j = i) (x : Fin (c 0) → K) :
    (chainMat Kj j).mulVec x = fun l => ((chainMat Kj i).mulVec x) (Fin.cast (congrArg c h) l) := by
  subst h
  rfl

theorem ChainTie.evidence (T : ChainTie ch Q) {f : (Fin (ch.c 0) → K) →ₗ[K] (Q.F 0).Forms}
    {g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)} (h0 : T.First f) (hL : T.Last g)
    (φ : Fin (Dc.a u) → K) (F : Fin (Df.nV Bs.μ0) → K) :
    Dc.Pt u Bs.μ0 φ F = g (Q.col (f fun i => φ (Fin.cast ch.c0 i))) F := by
  rw [ch.fact φ F, chainMat_mulVec_cast ch.Kj ⟨Q.n + 1, by have := T.hmm; omega⟩ (Fin.last ch.mm) T.last_eq]
  rw [hL, T.chain]
  exact congrArg (fun z => g (Q.col z) F) (h0 _)

theorem ChainTie.col_isom (T : ChainTie ch Q)
    (hN : ∀ (v : InfinitePlace K) (x : Fin (ch.c ⟨0, by omega⟩) → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨Q.n + 1, by have := T.hmm; omega⟩))) (ch.X ⟨Q.n + 1, by have := T.hmm; omega⟩) v
                ((chainMat ch.Kj ⟨Q.n + 1, by have := T.hmm; omega⟩).mulVec x) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨0, by omega⟩))) (ch.X ⟨0, by omega⟩) v x)
    (v : InfinitePlace K) (x : Fin (ch.c 0) → K) :
    Q.S₁.ipAt Q.hS₁ v (Q.col (T.coF 0 (Nat.zero_le _) x)) (Q.col (T.coF 0 (Nat.zero_le _) x)) =
      famIpAt (Q.F 0) (Q.hF 0) v (T.coF 0 (Nat.zero_le _) x) (T.coF 0 (Nat.zero_le _) x) := by
  rw [← T.chain x, ← T.metL v, hN v x]
  exact T.metF 0 (Nat.zero_le _) v x

end Comparison₂

section ColFace

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} (W : Wts X Pr.Word Rk) (Ch : Chars X Pr Rk.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K)))

abbrev ramDim (u : Pr.Word) : ℕ := (colGSD W Ch u 0).subD (colOk W Ch hX u 0) (MramV W Ch u)

abbrev ramBas (u : Pr.Word) : Basis (Fin (ramDim W Ch hX u)) X.K (MramV W Ch u) :=
  (colGSD W Ch u 0).subB (colOk W Ch hX u 0) (MramV W Ch u)

def colOfCoord (u : Pr.Word) : (Fin (ramDim W Ch hX u) → X.K) →ₗ[X.K] MfV W Ch u :=
  (MramV W Ch u).subtype ∘ₗ (ramBas W Ch hX u).equivFun.symm.toLinearMap

def colsIn {m2 : ℕ} {G : ChGlob X Rk.m} (hL : L.Ok Ch sel mu cst G m2) (u : Pr.Word) :
    (Fin (ramDim W Ch hX u) → X.K) →ₗ[X.K] (chF W sel mu L u 0).Forms :=
  startC hL u ∘ₗ colOfCoord W Ch hX u

variable {W Ch sel mu cst L}

def colPerL {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    (u : Pr.Word) {n : ℕ} (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P) :
    (evGSD W Ch sel mu P u).EqFun →ₗ[X.K] Module.Dual X.K (Fin n → X.K) :=
  (PtilFF W Ch sel mu P hP u).compl₁₂ (evGSD W Ch sel mu P u).EqFun.subtype
    ((mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ (V0X W Ch sel mu Xg P).subtype ∘ₗ ev)

def colPer {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X Rk.m} (hL : L.Ok Ch sel mu cst G m2) {n : ℕ}
    (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P) :
    (Fin (ramDim W Ch hX u) → X.K) →ₗ[X.K] Module.Dual X.K (Fin n → X.K) :=
  ((BtOf W Ch sel mu P hP Xg u (colC A hF hL)).compl₂ ev) ∘ₗ (ramBas W Ch hX u).equivFun.symm.toLinearMap

theorem colPer_eq {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) {G : ChGlob X Rk.m} (hL : L.Ok Ch sel mu cst G m2) {n : ℕ}
    (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P) (φ : Fin (ramDim W Ch hX u) → X.K) (F : Fin n → X.K) :
    colPer hX hP Xg A hF hL ev φ F =
      colPerL hP Xg u ev ((KerChain.ofCol W Ch sel mu cst L A hF hE).col (colsIn W Ch hX sel mu cst L hL u φ)) F := rfl

end ColFace

section ColFaceAll

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

def colFace (hX : X.Ok) {Bs : DefBase X.K} (Df : DefSide Bs) {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    {m2 : ℕ} {G : ChGlob X Rk.m} (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) G m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (A : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x)) (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P) : DefCols Df where
  Mem := Mem
  a x := ramDim W Ch hX (wd x)
  Xc x := (MramH W Ch hX (wd x)).X
  Pt x t := colPer hX (hP t) Xg (A t x) (hF t x) (hL t) (ev t)

section Face

variable {hX : X.Ok} {Bs : DefBase X.K} {Df : DefSide Bs} {P : LevFam X.E X.K Rk.r Pr.vGs}
  {Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)} {m2 : ℕ} {G : ChGlob X Rk.m} {mu : Bs.Tup → Tup X.F X.E X.K Sg}
  {cst : ∀ t, LocCst X (rowSG Pr sel (mu t))} {L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))}
  {hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) G m2} {hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok}
  {Mem : Type} {wd : Mem → Pr.Word} {b : ∀ t, Mem → (L t).β (m2 + 1)}
  {hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x)}
  {A : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x)}
  {hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok} {ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P}

theorem colFace_pt (x : Mem) (t : Bs.Tup) :
    (colFace hX Df Xg mu cst L hL hP Mem wd b hY A hF ev).Pt x t = colPer hX (hP t) Xg (A t x) (hF t x) (hL t) (ev t) := rfl

theorem colFace_a (x : Mem) : (colFace hX Df Xg mu cst L hL hP Mem wd b hY A hF ev).a x = ramDim W Ch hX (wd x) := rfl

theorem colFace_Xc (x : Mem) : (colFace hX Df Xg mu cst L hL hP Mem wd b hY A hF ev).Xc x = (MramH W Ch hX (wd x)).X := rfl

variable (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) P (wd x)).Ok) {x : Mem}
  {ch : ColChain (colFace hX Df Xg mu cst L hL hP Mem wd b hY A hF ev) x}

abbrev memQ : KerChain X.K :=
  KerChain.ofCol W Ch sel (mu Bs.μ0) (cst Bs.μ0) (L Bs.μ0) (A Bs.μ0 x) (hF Bs.μ0 x) (hE x)

def FirstCols (T : ChainTie ch (memQ (A := A) (hF := hF) hE (x := x))) : Prop :=
  T.First ((colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (L Bs.μ0) (hL Bs.μ0) (wd x)).comp
    (LinearMap.funLeft X.K X.K (Fin.cast ch.c0.symm)))

def LastPer (T : ChainTie ch (memQ (A := A) (hF := hF) hE (x := x))) : Prop :=
  T.Last (colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0))

theorem FirstCols.chain {T : ChainTie ch (memQ (A := A) (hF := hF) hE (x := x))} (h0 : FirstCols hE T) (y : Fin (ch.c 0) → X.K) :
    T.coL ((chainMat ch.Kj ⟨(memQ (A := A) (hF := hF) hE (x := x)).n + 1, by have := T.hmm; omega⟩).mulVec y) =
      colC (A Bs.μ0 x) (hF Bs.μ0 x) (hL Bs.μ0) (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast ch.c0.symm i)) := by
  rw [T.chain y, h0 y]
  rfl

theorem colFace_fact (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin (Df.nV Bs.μ0) → X.K) :
    ch.PtL ((chainMat ch.Kj (Fin.last ch.mm)).mulVec fun i => φ (Fin.cast ch.c0 i)) F =
      colPer hX (hP Bs.μ0) Xg (A Bs.μ0 x) (hF Bs.μ0 x) (hL Bs.μ0) (ev Bs.μ0) φ F := (ch.fact φ F).symm

theorem LastPer.reading_tie {T : ChainTie ch (memQ (A := A) (hF := hF) hE (x := x))} (h0 : FirstCols hE T)
    (hL' : LastPer hE T) (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin (Df.nV Bs.μ0) → X.K) :
    (colFace hX Df Xg mu cst L hL hP Mem wd b hY A hF ev).Pt x Bs.μ0 φ F =
      colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0) (colC (A Bs.μ0 x) (hF Bs.μ0 x) (hL Bs.μ0) (colOfCoord W Ch hX (wd x) φ)) F := by
  rfl

theorem FirstCols.isom {T : ChainTie ch (memQ (A := A) (hF := hF) hE (x := x))} (h0 : FirstCols hE T)
    (hN : ∀ (v : InfinitePlace X.K) (y : Fin (ch.c ⟨0, by omega⟩) → X.K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ch.c ⟨(memQ (A := A) (hF := hF) hE (x := x)).n + 1, by have := T.hmm; omega⟩)))
                (ch.X ⟨(memQ (A := A) (hF := hF) hE (x := x)).n + 1, by have := T.hmm; omega⟩) v
                ((chainMat ch.Kj ⟨(memQ (A := A) (hF := hF) hE (x := x)).n + 1, by have := T.hmm; omega⟩).mulVec y) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ch.c ⟨0, by omega⟩))) (ch.X ⟨0, by omega⟩) v y)
    (v : InfinitePlace X.K) (y : Fin (ch.c 0) → X.K) :
    (evGSD W Ch sel (mu Bs.μ0) P (wd x)).ipAt (hE x) v
        (colC (A Bs.μ0 x) (hF Bs.μ0 x) (hL Bs.μ0) (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast ch.c0.symm i)))
        (colC (A Bs.μ0 x) (hF Bs.μ0 x) (hL Bs.μ0) (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast ch.c0.symm i))) =
      famIpAt (chF W sel (mu Bs.μ0) (L Bs.μ0) (wd x) 0) (hF Bs.μ0 x 0) v
        (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (L Bs.μ0) (hL Bs.μ0) (wd x) fun i => y (Fin.cast ch.c0.symm i))
        (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (L Bs.μ0) (hL Bs.μ0) (wd x) fun i => y (Fin.cast ch.c0.symm i)) := by
  have h := T.col_isom hN v y
  rw [h0 y] at h
  exact h

end Face

end ColFaceAll

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

def DivClauses {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCore Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  (∀ φ ∈ shiftLat Nu sg, P.cols.col.B u φ ∈ Formalism.HN.dualLat P.cols.RR) ∧
  (∃ cu : InfinitePlace K → ℝ, (∀ v, 0 < cu v ∧
      Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
        (Formalism.HN.dualFrame P.cols.XE) v (P.cols.col.B u) ^ 2 ≤ cu v) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (cu v) = R.hu - meanLog P.cols.κ) ∧
  P.cols.muCC - meanLog P.cols.κ + R.hu - 2 * FoOf P ≤ R.rhs ∧
  Formalism.HN.muDef (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (shiftLat Nu sg) =
    Formalism.HN.muDef (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) Nu +
      2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (shiftZ sg w : ℝ)

theorem nK_of_cb {m : ℕ} {c : Fin (m + 1) → ℕ} {Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ}
    {Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K} (D : CBData Xc Kj) (B : Fin m → InfinitePlace K → ℝ)
    (hB : ∀ j v, Real.log (D.sq j v) ≤ B j v) (j : Fin m) (v : InfinitePlace K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v
      (Matrix.mulVecLin (Kj j)) ^ 2 ≤ Real.exp (B j v) := by
  have H := Formalism.DimensionVariation.chain_coupled_bound K m c Xc Kj D.AA D.Cl D.W D.γ D.Φ D.ε D.T D.hcl D.tmax D.hyp
    (fun j v => Real.sqrt (D.sq j v)) (fun _ _ => rfl)
  have h1 := H.1 j v
  have h2 : Real.sqrt (D.sq j v) ^ 2 = D.sq j v := H.2.1 j v
  have h0 := OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) (Pi.basisFun K (Fin (c j.succ)))
    (Xc j.succ) v (Matrix.mulVecLin (Kj j))
  have h3 : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v
      (Matrix.mulVecLin (Kj j)) ^ 2 ≤ D.sq j v := by
    rw [← h2]; exact pow_le_pow_left₀ h0 h1 2
  rcases le_or_gt (D.sq j v) 0 with hs | hs
  · exact h3.trans (hs.trans (Real.exp_pos _).le)
  · calc _ ≤ D.sq j v := h3
      _ = Real.exp (Real.log (D.sq j v)) := (Real.exp_log hs).symm
      _ ≤ Real.exp (B j v) := Real.exp_le_exp.2 (hB j v)

theorem exists_cu {ι : Type} [Fintype ι] [Nonempty ι] (x a : ι → ℝ) (t : ℝ) (hx : ∀ v, 0 ≤ x v)
    (ha : ∀ v, x v = 0 ∨ Real.log (x v ^ 2) ≤ a v) (hm : (1 / (Fintype.card ι : ℝ)) * ∑ v, a v ≤ t) :
    ∃ cu : ι → ℝ, (∀ v, 0 < cu v ∧ x v ^ 2 ≤ cu v) ∧ (1 / (Fintype.card ι : ℝ)) * ∑ v, Real.log (cu v) = t := by
  refine ⟨fun v => Real.exp (a v + (t - (1 / (Fintype.card ι : ℝ)) * ∑ w, a w)), fun v => ⟨Real.exp_pos _, ?_⟩, ?_⟩
  · by_cases h0 : x v = 0
    · rw [h0]
      nlinarith [Real.exp_pos (a v + (t - (1 / (Fintype.card ι : ℝ)) * ∑ w, a w))]
    · have hl := (ha v).resolve_left h0
      have hpos : 0 < x v ^ 2 := pow_pos (lt_of_le_of_ne (hx v) (Ne.symm h0)) 2
      calc x v ^ 2 = Real.exp (Real.log (x v ^ 2)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (a v + (t - (1 / (Fintype.card ι : ℝ)) * ∑ w, a w)) := Real.exp_le_exp.mpr (by linarith)
  · have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Real.log_exp]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

theorem complex_height_cast_at (hH : HeightBoundConstant) {K : Type} [Field K] [NumberField K] [StarRing K] {a n dQ D m : ℕ}
    (c : Fin (m + 1) → ℕ) (c0 : c 0 = a) (hd : dQ = D)
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (hXc : ∀ i v, IsUnit (Xc i v).det)
    (hXz : ∀ v i j, Xc 0 v i j = Xa v (Fin.cast c0 i) (Fin.cast c0 j))
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin dQ) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin dQ) (Fin dQ) ℂ) (hXQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin dQ) K) (hι : Function.Bijective ι.mulVec)
    (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin dQ → K)) (hQp : (⨆ p, Qp p) = ⊤)
    (κ : InfinitePlace K → ℝ) (lam : J → Ix → InfinitePlace K → ℝ) (hκ : ∀ v, 0 < κ v) (hlam : ∀ j p v, 0 < lam j p v)
    (hsc : ∀ v p, IsScalarOn XQ XE v ι (Qp p) (κ v * ∏ j, lam j p v))
    (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec fun i => φ (Fin.cast c0 i)) F)
    (hne : B ≠ 0) (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v)
    (hkU : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) (v : InfinitePlace K) :
    Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
      Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) - minOver (fun p => ∑ j, Real.log (lam j p v)) := by
  subst c0 hd
  obtain rfl : Xc 0 = Xa := by
    funext v; ext i j; simpa using hXz v i j
  exact (hH K n dQ m c Xc hXc Kj H X0 hX0 P hP XQ hXQ XE hXE ι (isUnit_det_of_bij _ hι) Ix J Qp hQp κ lam lam hκ hlam
    (fun _ _ _ => le_rfl) hsc Pt B (by simpa using hB) hne pU kU hpU hkU).1 v

theorem nonempty_Ix {Df : DefSide Bs} (wf : Df.WF) (hpos : Df.Pos) : Nonempty Bs.Ix := by
  by_contra h
  rw [not_nonempty_iff] at h
  have ht := wf.Qp_top
  rw [iSup_of_empty] at ht
  have : Nonempty (Fin (Df.dQ Bs.μ0)) := ⟨⟨0, hpos⟩⟩
  exact bot_ne_top ht

theorem height_chain {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} [Nonempty Bs.Ix] (wf : Df.WF)
    (S : IndefCols Df Dc Sp N) (u : Dc.Mem) (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (ch : ColChain Dc u) (hP : ℝ) (hK : Bs.J → InfinitePlace K → ℝ)
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hP)
    (nK : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c j.castSucc))) (ch.X j.castSucc)
      (Pi.basisFun K (Fin (ch.c j.succ))) (ch.X j.succ) v (Matrix.mulVecLin (ch.Kj j)) ^ 2 ≤
        Real.exp (∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v)) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
              (Formalism.HN.dualFrame S.XE) (S.col.B u) ≤
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) - ∑ j, N.l6 j - meanLog S.κ := by
  have hc := S.l1c
  have hb := S.l1b
  have hsc : ∀ v p, IsScalarOn (Df.XQ Bs.μ0) S.XE v (S.ι Bs.μ0) (Df.Qp Bs.μ0 p)
      (S.κ v * ∏ j, S.lam j Bs.μ0 p v) := fun v p => by
    rw [← S.toIndefRows.Qpart_base p]; exact hc.2.2.2.2.1 Bs.μ0 v (Or.inl rfl) p
  have H := complex_height_cast height_constant_bound ch.c ch.c0 (S.toIndefRows.dQ_eq Bs.μ0) (Dc.Xc u) ch.X ch.X_unit ch.X_zero ch.Kj
    (Df.HV Bs.μ0) X0 hX0 (Df.Pq Bs.μ0) (wf.Pq_surj _) (Df.XQ Bs.μ0) (wf.XQ_quot _) S.XE S.frames.1 (S.ι Bs.μ0) (hc.1 _)
    Bs.Ix Bs.J (Df.Qp Bs.μ0) wf.Qp_top S.κ (fun j p v => S.lam j Bs.μ0 p v) hc.2.2.1 (fun j p v => hc.2.2.2.1 j _ p v) hsc
    ch.PtL (S.col.B u)
    (fun φ F => by
      have h1 := hb.1 u Bs.μ0 φ F
      rw [hb.2.1 u, one_mul] at h1
      rw [← h1]; exact ch.fact φ F)
    hne (fun _ => Real.exp (hP / 2)) (fun j v => Real.exp ((∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) / 2))
    (fun v => le_exp_half (nP v)) (fun j v => le_exp_half (nK j v))
  simp only [log_exp_half_sq] at H
  have hn : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    exact_mod_cast this
  have h2 : ∑ j, N.l6 j ≤ (1 / (Formalism.HN.nPl K : ℝ)) *
      ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := by
    have h3 : ∑ _v : InfinitePlace K, ∑ j, N.l6 j ≤
        ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := Finset.sum_le_sum fun v _ => S.log_eigenvalue_sum_le_min v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    rw [one_div, le_inv_mul_iff₀ (by exact hn)]
    exact h3
  have h4 : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) =
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) := by
    have e1 : ∀ v, ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v = ∑ j, hK j v := fun v =>
      Finset.sum_fiberwise Finset.univ ch.lf (fun l => hK l v)
    simp only [e1]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm, ← Finset.sum_div]
    show (1 / (Fintype.card (InfinitePlace K) : ℝ)) * _ = _
    field_simp
  rw [h4] at H
  linarith [H, h2]

theorem height_chain_at {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} [Nonempty Bs.Ix] (wf : Df.WF)
    (S : IndefCols Df Dc Sp N) (u : Dc.Mem) (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (ch : ColChain Dc u) (hP : ℝ) (hK : Bs.J → InfinitePlace K → ℝ)
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hP)
    (nK : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c j.castSucc))) (ch.X j.castSucc)
      (Pi.basisFun K (Fin (ch.c j.succ))) (ch.X j.succ) v (Matrix.mulVecLin (ch.Kj j)) ^ 2 ≤
        Real.exp (∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v)) :
    (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
        (Formalism.HN.dualFrame S.XE) v (S.col.B u) ^ 2) ≤
      hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v - Real.log (S.κ v) -
        minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) ∧
    (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v -
        Real.log (S.κ v) - minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) ≤
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) - ∑ j, N.l6 j - meanLog S.κ := by
  have hc := S.l1c
  have hb := S.l1b
  have hsc : ∀ v p, IsScalarOn (Df.XQ Bs.μ0) S.XE v (S.ι Bs.μ0) (Df.Qp Bs.μ0 p)
      (S.κ v * ∏ j, S.lam j Bs.μ0 p v) := fun v p => by
    rw [← S.toIndefRows.Qpart_base p]; exact hc.2.2.2.2.1 Bs.μ0 v (Or.inl rfl) p
  have Hv := fun v => complex_height_cast_at height_constant_bound ch.c ch.c0 (S.toIndefRows.dQ_eq Bs.μ0) (Dc.Xc u) ch.X ch.X_unit ch.X_zero
    ch.Kj (Df.HV Bs.μ0) X0 hX0 (Df.Pq Bs.μ0) (wf.Pq_surj _) (Df.XQ Bs.μ0) (wf.XQ_quot _) S.XE S.frames.1 (S.ι Bs.μ0) (hc.1 _)
    Bs.Ix Bs.J (Df.Qp Bs.μ0) wf.Qp_top S.κ (fun j p v => S.lam j Bs.μ0 p v) hc.2.2.1 (fun j p v => hc.2.2.2.1 j _ p v) hsc
    ch.PtL (S.col.B u)
    (fun φ F => by
      have h1 := hb.1 u Bs.μ0 φ F
      rw [hb.2.1 u, one_mul] at h1
      rw [← h1]; exact ch.fact φ F)
    hne (fun _ => Real.exp (hP / 2)) (fun j v => Real.exp ((∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) / 2))
    (fun v => le_exp_half (nP v)) (fun j v => le_exp_half (nK j v)) v
  simp only [log_exp_half_sq] at Hv
  refine ⟨Hv, ?_⟩
  have hn : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    exact_mod_cast this
  have h2 : ∑ j, N.l6 j ≤ (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
      ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := by
    have h3 : ∑ _v : InfinitePlace K, ∑ j, N.l6 j ≤
        ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) := Finset.sum_le_sum fun v _ => S.log_eigenvalue_sum_le_min v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    rw [one_div, le_inv_mul_iff₀ (by exact hn)]
    exact h3
  have h4 : (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) =
      hP + ∑ j, (∑ v, hK j v) / (Fintype.card (InfinitePlace K) : ℝ) := by
    have e1 : ∀ v, ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v = ∑ j, hK j v := fun v =>
      Finset.sum_fiberwise Finset.univ ch.lf (fun l => hK l v)
    simp only [e1]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm, ← Finset.sum_div]
    field_simp
  have e : (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v -
        Real.log (S.κ v) - minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v))) =
      (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (hP + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hK l v) -
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, minOver (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) - meanLog S.κ := by
    simp only [meanLog, Finset.sum_sub_distrib]
    show _ = _ - _ - (1 / (Fintype.card (InfinitePlace K) : ℝ)) * _
    ring
  rw [e, h4]
  linarith [h2]

theorem divClauses_of [IsTotallyComplex K] {Pl : Type} [Fintype Pl] [DecidableEq Pl] (wf0 : Df0.WF) (wf1 : Df1.WF)
    (P : IndefCore Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl) (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (sg : HeightOneSpectrum (𝓞 K) → ℝ) (I : DivInputs P R u Nu sg) : DivClauses P R u Nu sg := by
  have : Nonempty Bs.Ix := nonempty_Ix wf0 P.base.pos
  have hsh := shiftEx K (Dc.a u) Nu I.Nu_lat (shiftZ sg) I.sg_fin
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact P.cols.intoDual divIntoDualShift latticeGlue wf1 u Nu (shiftLat Nu sg) sg (shiftZ sg) I.val2
      (fun w => Int.floor_le_ceil _) hsh.1
  ·
    have hX := fun v => OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
      (Formalism.HN.dualFrame P.cols.XE) v (P.cols.col.B u)
    by_cases hne : P.cols.col.B u = 0
    · refine exists_cu _ (fun _ => R.hu - meanLog P.cols.κ) _ hX (fun v => Or.inl ?_) (le_of_eq ?_)
      · rw [hne]; simp [Formalism.HN.opNormAt]
      · have hn : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by
          have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
          exact_mod_cast this
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    · have nK := nK_of_cb I.cb (fun j v => ∑ l ∈ Finset.univ.filter (fun l => I.ch.lf l = j), I.hn.sz l v) I.nKcb
      obtain ⟨Hv, Hm⟩ := height_chain_at wf1 P.cols u hne I.X0 I.base_matrix_det_unit I.ch I.hn.hPn I.hn.sz I.nP nK
      have h1 := I.hn.le_hu (∑ j, N.l6 j) I.eig6
      refine exists_cu _ (fun v => I.hn.hPn + ∑ j, ∑ l ∈ Finset.univ.filter (fun l => I.ch.lf l = j), I.hn.sz l v -
        Real.log (P.cols.κ v) - minOver (fun p => ∑ j, Real.log (P.cols.lam j Bs.μ0 p v))) _ hX (fun v => Or.inr (Hv v)) ?_
      linarith [Hm, h1]
  ·
    have hB := P.base.boundsMu Formalism.DivisorInequality.boundsMu specDet reduction_lemma_zero latticeGlue ramBasic wf0 P.extra.untw I.eb I.heb
      I.Sy I.Sy_tw I.G0 I.LG I.E3 I.E2 I.gy I.ηy I.bi I.bLG I.biv I.borderedMinorImage I.twisted_third_sum_le
    have de0 : 0 ≤ N.de := I.de0
    have deQ : 3 * N.de * I.Q ≤ 1 := I.deQ
    have de3 : N.de ≤ 1 / 3 := by nlinarith [I.Q1]
    have hp := (P.extra.passage de0 de3 _ P.extra.fun0).2
    have hκ : P.cols.κ = P.base.κ := P.extra.level.2.1.symm
    set mu0 : ℝ := P.base.muCC - meanLog P.base.κ with hmu0def
    have hmu0 : mu0 ≤ boundB P I.LG I.E3 I.E2 := by
      have : P.base.muCC ≤ meanLog P.base.κ + (∑ j, N.l3 j) +
          2 * (∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + I.LG +
          (∑ j, (N.E1 j + I.E2 j)) + I.E3 := hB
      simp only [boundB, FoOf, hmu0def]
      linarith
    have hpass : 3 * N.de * (mu0 + N.hh + 28 * N.la) + 28 * N.la ≤ 1 + R.C0 * (R.m * R.lam0) := by
      have h1 : 3 * N.de * (mu0 + N.hh + 28 * N.la) ≤ 3 * N.de * I.Q :=
        mul_le_mul_of_nonneg_left (by linarith [I.Qb]) (by linarith)
      have h2 : 28 * R.lam0 ≤ R.C0 * (R.m * R.lam0) := by
        have h3 : R.lam0 ≤ R.m * R.lam0 := by nlinarith [R.p14, R.p35]
        nlinarith [I.constant_ge_twenty_eight, R.p35, R.c1]
      linarith [I.la_le]
    have hC : P.cols.muCC - meanLog P.cols.κ ≤ mu0 + (3 * N.de * (mu0 + N.hh + 28 * N.la) + 28 * N.la) := by
      rw [hκ, hmu0def]
      have : P.cols.muCC ≤ P.base.muCC + 3 * N.de * (P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la) +
          28 * N.la := hp
      have e : P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la =
          P.base.muCC - meanLog P.base.κ + N.hh + 28 * N.la := by ring
      rw [e] at this
      linarith
    have hM : mu0 ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + 2 * FoOf P +
        (I.El3 + I.LG + (∑ j, (N.E1 j + I.E2 j)) + I.E3) := by
      have h1 := I.L3main
      have h2 : boundB P I.LG I.E3 I.E2 = (∑ j, N.l3 j) + 2 * FoOf P + I.LG + (∑ j, (N.E1 j + I.E2 j)) + I.E3 := rfl
      linarith
    exact R.divIneq _ mu0 (FoOf P) _ _ hC hM hpass I.errB
  ·
    exact ((shiftMu K (Dc.a u) (Dc.Xc u) I.Xc_unit Nu (shiftLat Nu sg) I.Nu_lat hsh.2.1 (shiftZ sg) hsh.1).2 I.a_pos).2

theorem DivClauses.height [IsTotallyComplex K] {Pl : Type} [Fintype Pl] [DecidableEq Pl] {P : IndefCore Df0 Df1 Dc Sp N}
    {R : RecNums Bs.J Pl} {u : Dc.Mem} {Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : DivClauses P R u Nu sg)
    (hpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
      (Formalism.HN.dualFrame P.cols.XE) v (P.cols.col.B u)) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
      (Formalism.HN.dualFrame P.cols.XE) (P.cols.col.B u) ≤ R.hu - meanLog P.cols.κ := by
  obtain ⟨_, ⟨cu, hcu, hmean⟩, _⟩ := h
  unfold Formalism.HN.htMap
  rw [← hmean]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro v _
  exact Real.log_le_log (pow_pos (hpos v) 2) (hcu v).2

theorem eigen_sum_le_of_scale {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Z : IndefScale Bs) (C CH : ℝ) (R : RecNums Bs.J Pl)
    (h1 : ∀ j, ∑ ρ, R.logH j ρ ≤ Z.l6m j) (h2 : C * Z.l6u ≤ R.Ch * R.f * R.nV ^ 2 * R.Lp) :
    ∑ j, R.hX j ≤ ∑ j, (Z.num C CH).l6 j := Finset.sum_le_sum fun j _ => by
    show (∑ ρ, R.logH j ρ) - R.Ch * R.f * R.nV ^ 2 * R.Lp ≤ Z.l6m j - C * Z.l6u
    linarith [h1 j]

theorem l3main_of_scale {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Z : IndefScale Bs) (C CH : ℝ) (R : RecNums Bs.J Pl)
    (h : ∀ j, Z.l3m j ≤ ∑ ρ, R.pq j * R.w j ρ * R.logOm) :
    ∑ j, (Z.num C CH).l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + R.m * (C * Z.l3u) := by
  show ∑ j, (Z.l3m j + C * Z.l3u) ≤ _
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12]
  have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h j
  linarith

theorem errB_of_units {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Z : IndefScale Bs) (C CH : ℝ) (R : RecNums Bs.J Pl)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (c3 cG c2 cE : ℝ) (hC : 0 ≤ C)
    (hE1 : Z.E1u ≤ R.x ^ R.eps * (R.B0 + R.Nc)) (hl3 : C * Z.l3u ≤ c3 * (R.x ^ R.eps * (R.B0 + R.Nc)))
    (hLG : LG ≤ cG * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc)))) (hE2 : ∀ j, E2 j ≤ c2 * (R.x ^ R.eps * (R.B0 + R.Nc)))
    (hE3 : E3 ≤ cE * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc)))) (hce : c3 + cG + C + c2 + cE ≤ R.ce) :
    R.m * (C * Z.l3u) + LG + (∑ j, ((Z.num C CH).E1 j + E2 j)) + E3 ≤ R.errB := by
  have hU := R.unit_nonneg
  have hm : 0 ≤ R.m := by linarith [R.p14]
  have hmU : 0 ≤ R.m * (R.x ^ R.eps * (R.B0 + R.Nc)) := mul_nonneg hm hU
  show R.m * (C * Z.l3u) + LG + (∑ j, (C * Z.E1u + E2 j)) + E3 ≤ R.ce * R.m * (R.x ^ R.eps * (R.B0 + R.Nc))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12]
  have hE2s : ∑ j, E2 j ≤ ∑ _j : Bs.J, c2 * (R.x ^ R.eps * (R.B0 + R.Nc)) := Finset.sum_le_sum fun j _ => hE2 j
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12] at hE2s
  have a1 : R.m * (C * Z.l3u) ≤ R.m * (c3 * (R.x ^ R.eps * (R.B0 + R.Nc))) := mul_le_mul_of_nonneg_left hl3 hm
  have a2 : R.m * (C * Z.E1u) ≤ R.m * (C * (R.x ^ R.eps * (R.B0 + R.Nc))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE1 hC) hm
  have a3 : (c3 + cG + C + c2 + cE) * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc))) ≤
      R.ce * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc))) :=
    mul_le_mul_of_nonneg_right hce hmU
  linarith

theorem bi_of_cut [IsTotallyComplex K] {Df : DefSide Bs} (wf : Df.WF) (t : Bs.Tup) {n' : ℕ}
    (H' : Matrix (Fin n') (Fin n') K) (hH : H'ᴴ = H') (hH' : IsUnit H'.det)
    (E : Matrix (Fin n') (Fin (Df.nV t)) K) (Pr : Matrix (Fin (Df.nV t)) (Fin n') K) (hE : IsOrthProj H' E Pr)
    (hHV : Df.HV t = Eᴴ * H' * E) (A B : Submodule (𝓞 K) (Fin n' → K)) (hA : Submodule.IsLattice K A)
    (hMt : Df.Mt t = cutLat E A) (s : ℕ) (hs : 0 < s) (hsA : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B)
    (G : ℕ) (hG : 0 < G) (hGB : ∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K) (y : HeightOneSpectrum (𝓞 K))
    (heb : IsLocBasis (Df.abelian₂ t) y (eb t y)) :
    (vw y (Df.Gm eb t y) : ℝ) ≤ (Df.dQ t : ℝ) * ((vw y (G : K) : ℝ) + (vw y (s : K) : ℝ)) := by
  have h := boundsIVal K Bs.K0 wf.cm Bs.v0 wf.conj n' (Df.nV t) (Df.dQ t) H' hH hH' E Pr hE
    (fun i j => hHV ▸ wf.HV_rat t i j) (fun v => hHV ▸ wf.HV_pos t v) (Df.Pq t) (wf.Pq_surj t) A B hA s hs hsA G hG hGB y
    (eb t y) (by rw [← hMt]; exact heb)
  rw [← hHV] at h
  have h' : vw y (Df.Gm eb t y) ≤ (Df.dQ t : ℤ) * (vw y (G : K) + vw y (s : K)) := h
  exact_mod_cast h'

end Generic

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def faceOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : DefSub A.fam.amb → DefFace A.fam.base :=
  fun Zs => ⟨A.side P0 ψ0 Zs, A.side P1 ψ1 Zs, Dc Zs, Sp Zs, Zsc Zs⟩

theorem division_height_bound_clauses [IsTotallyComplex K] (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputs Pk.core R u Nu sg) : DivClauses Pk.core R u Nu sg := divClauses_of (A.side_WF hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep) (A.side_WF hOk P1 ψ1 Pk.Zs Pk.stable Pk.inBlock hsep)
    Pk.core R u Nu sg I

end Concrete

section ConcreteCol

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem division_height_bound [IsTotallyComplex X.K] (A : FamIn X.K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) (hX : X.Ok)
    {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m}
    (mu : A.fam.base.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Ak : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x))
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu A.fam.base.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY Ak hF (ev Zs)))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb
      (faceOf A P0 ψ0 P1 ψ1 (fun Zs => colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY Ak hF (ev Zs)) Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputs Pk.core R x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := Ak) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) (hPL : LastPer hE hQ) :
    DivClauses Pk.core R x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := Ak) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          colC (Ak A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0)
            (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP A.fam.base.μ0) Xg (wd x) (ev Pk.Zs A.fam.base.μ0)
            (colC (Ak A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0) (colOfCoord W Ch hX (wd x) φ)) F := ⟨division_height_bound_clauses A hOk hsep P0 ψ0 P1 ψ1 _ Sp Zsc C CH Pk R x Nu sg I, fun y => FirstCols.chain hE h0 y,
    fun φ F => colFace_fact (ch := I.ch) φ F⟩

abbrev kerRec {Bs : DefBase X.K} {P : LevFam X.E X.K Rk.r Pr.vGs} {m2 : ℕ} (mu : Bs.Tup → Tup X.F X.E X.K Sg)
    (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) {Mem : Type}
    (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1)) (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P) :
    ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x) :=
  fun t x => Formalism.L2.Ker.chKerC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x)

theorem kerRec_colC {Bs : DefBase X.K} {P : LevFam X.E X.K Rk.r Pr.vGs} {m2 : ℕ} {Gc : ChGlob X Rk.m} (mu : Bs.Tup → Tup X.F X.E X.K Sg)
    (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K)))
    (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2) {Mem : Type}
    (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1)) (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (t : Bs.Tup) (x : Mem) :
    colC (kerRec mu cst L wd b hY Am hK t x) (hF t x) (hL t) =
      Formalism.L2.Ker.colMu W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x) (hF t x) (hL t) := rfl

theorem division_height_bound_at_sizeData [IsTotallyComplex X.K] (A : FamIn X.K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) (hX : X.Ok)
    {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m}
    (mu : A.fam.base.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu A.fam.base.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb
      (faceOf A P0 ψ0 P1 ψ1 (fun Zs => colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)) Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputs Pk.core R x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) :
    DivClauses Pk.core R x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          Formalism.L2.Ker.colMu W Ch sel (mu A.fam.base.μ0) (cst A.fam.base.μ0) (L A.fam.base.μ0) Am (wd x) m2 (b A.fam.base.μ0 x) (hY A.fam.base.μ0 x) P
            (hK A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0) (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP A.fam.base.μ0) Xg (wd x) (ev Pk.Zs A.fam.base.μ0)
            (Formalism.L2.Ker.colMu W Ch sel (mu A.fam.base.μ0) (cst A.fam.base.μ0) (L A.fam.base.μ0) Am (wd x) m2 (b A.fam.base.μ0 x) (hY A.fam.base.μ0 x) P
              (hK A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0) (colOfCoord W Ch hX (wd x) φ)) F := ⟨division_height_bound_clauses A hOk hsep P0 ψ0 P1 ψ1 _ Sp Zsc C CH Pk R x Nu sg I, fun y => FirstCols.chain hE h0 y,
    fun φ F => colFace_fact (ch := I.ch) φ F⟩

open Formalism.MainNotions in

theorem division_height_bound_statement [IsTotallyComplex X.K] (A : FamIn X.K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) (hX : X.Ok)
    {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m}
    (mu : A.fam.base.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    {D : D7} (sm : Formalism.L2.Ker.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) (Formalism.L2.Ker.ambOf sm B χ cD) (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu A.fam.base.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY
      (kerRec mu cst L wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK) hF (ev Zs)))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb
      (faceOf A P0 ψ0 P1 ψ1 (fun Zs => colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY
        (kerRec mu cst L wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK) hF (ev Zs)) Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputs Pk.core R x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := kerRec mu cst L wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK) (hF := hF) hE (x := x)))
    (h0 : FirstCols hE hQ) :
    DivClauses Pk.core R x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := kerRec mu cst L wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK) (hF := hF) hE (x := x)).n + 1,
            by have := hQ.hmm; omega⟩).mulVec y) =
          Formalism.L2.Ker.colMu W Ch sel (mu A.fam.base.μ0) (cst A.fam.base.μ0) (L A.fam.base.μ0) (Formalism.L2.Ker.ambOf sm B χ cD) (wd x) m2
            (b A.fam.base.μ0 x) (hY A.fam.base.μ0 x) P (hK A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0)
            (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP A.fam.base.μ0) Xg (wd x) (ev Pk.Zs A.fam.base.μ0)
            (Formalism.L2.Ker.colMu W Ch sel (mu A.fam.base.μ0) (cst A.fam.base.μ0) (L A.fam.base.μ0) (Formalism.L2.Ker.ambOf sm B χ cD) (wd x) m2
              (b A.fam.base.μ0 x) (hY A.fam.base.μ0 x) P (hK A.fam.base.μ0 x) (hF A.fam.base.μ0 x) (hL A.fam.base.μ0) (colOfCoord W Ch hX (wd x) φ)) F := division_height_bound_at_sizeData A hOk hsep P0 ψ0 P1 ψ1 hX Xg mu cst L hL hP Mem wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK hF hE ev Sp Zsc C CH Pk
    R x Nu sg I hQ h0

end ConcreteCol

end Formalism.L2.DIV

namespace Formalism.L2.DIV.Inst

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Examples₂ Formalism.L2.DIV
open Formalism.LatticeIndexTer (ph)

theorem e8 : (41 : ℝ) ≤ Real.exp 8 := by
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have h8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have h4' : (9 : ℝ) ≤ Real.exp 4 := by rw [h4]; nlinarith
  rw [h8]
  nlinarith

theorem l8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)

theorem l8' : Real.log 8 ≤ 7 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
  linarith

theorem La8 : Real.log (8 * Real.exp 8 * 1) = Real.log 8 + 8 := by
  rw [mul_one, Real.log_mul (by norm_num) (Real.exp_pos 8).ne', Real.log_exp]

theorem neg_three_le_phi_three : -3 ≤ ph 3 := by
  show -3 ≤ 3 * Real.log 3 - 3
  have h3 := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
  linarith

theorem ph32 : ph 3 - ph 2 ≤ 36 := by
  show (3 * Real.log 3 - 3) - (2 * Real.log 2 - 2) ≤ 36
  have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  linarith

def recNumsExample (J : Type) [Fintype J] [Unique J] (ce : ℝ) (hce : 36 ≤ ce) : RecNums J (Fin 1) where
  TT := Finset.univ
  logT := 1
  aT := fun _ => 2
  r := 1
  ν := fun _ _ _ => 3
  logH := fun _ _ => ph 3 - ph 2
  x := 8
  eps := 1
  L := 8
  b := Real.exp 8
  a := 8 * Real.exp 8
  rd := 1
  La := Real.log (8 * Real.exp 8 * 1)
  B0 := 1 * 1 * Real.exp 8 * (8 : ℝ) ^ (1 : ℝ)
  Nc := 1
  m := 1
  f := 1
  k := 1
  Nn := 2
  S := 0
  tt := 0
  η := 0
  w'' := 0
  b' := 1
  lam0 := 1
  C0 := 36
  ce := ce
  Ch := 36
  nV := 1
  Lp := 1
  logOm := 1 / 2
  pq := fun _ => 1
  w := fun _ _ => 1
  eE := fun _ _ => 0
  δ := fun _ _ => 0
  weight_height_sum_le := fun _ ρ => by fin_cases ρ; simp
  weight_sum_eq := fun _ ρ => by fin_cases ρ; simp; norm_num
  p1 := by norm_num
  p2 := one_pos
  p3 := (Real.rpow_one 8).symm
  p4 := rfl
  p5 := rfl
  p6 := le_refl _
  p7 := by simp
  p8 := by linarith [l8']
  p9 := rfl
  p10 := rfl
  p11 := zero_le_one
  p12 := by simp
  p13 := by simp
  p14 := le_refl _
  p15 := le_refl _
  p16 := le_refl _
  p17 := by norm_num
  p18 := le_refl _
  p19 := le_refl _
  p20 := le_refl _
  p21 := fun _ _ => ⟨zero_le_one, by linarith [e8]⟩
  p22 := fun _ => by simp
  p23 := by rw [La8, abs_of_pos (by norm_num)]; linarith [l8]
  p24 := by linarith [e8]
  p25 := by linarith [e8]
  p26 := by linarith [e8]
  p27 := by linarith [e8]
  p28 := by linarith [e8]
  p29 := by norm_num
  p30 := by norm_num
  p31 := by linarith [e8]
  p32 := by linarith [e8]
  p33 := by linarith [e8]
  p34 := zero_le_one
  p35 := zero_le_one
  p36 := zero_le_one
  p37 := by norm_num
  p38 := zero_le_one
  c1 := by norm_num
  c2 := hce
  c3 := by norm_num
  c4 := le_refl _
  c5 := by rw [La8]; linarith [l8]
  sE := fun _ _ => by rw [La8]; linarith [l8]
  sδ := fun _ ρ => by fin_cases ρ; simp; norm_num

def exampleHeightNumbers (J : Type) [Fintype J] [Unique J] (ce : ℝ) (hce : 36 ≤ ce) (Emb : Type) [Fintype Emb] [Nonempty Emb] :
    HtNums (recNumsExample J ce hce) Emb where
  hPn := 0
  g0 := fun _ => 0
  MainNotions := fun _ _ => 2
  logOmτ := fun _ _ => 1 / 2
  logth0 := fun _ => 0
  logh := fun _ => 0
  logh' := fun _ => 0
  vv := 0
  logg := 1
  C2 := 1
  Cth := 0
  C4 := 0
  c5 := 1
  c6 := 1
  CT := 1
  C8 := 1
  Ce := 1
  ev := 2
  bT := fun _ => 0
  nτ := fun _ => 3 / 2
  lam1 := fun _ => 3 / 2
  D0 := fun _ => 0
  D1 := fun _ => 0
  logc := fun _ => 0
  logxi := fun _ => 0
  Cev := 1
  i1 := fun _ => by
    have hn : (Fintype.card Emb : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    show (∑ _s : Emb, (1 / 2 : ℝ)) / (Fintype.card Emb : ℝ) = 1 / 2
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  i2 := fun _ _ => by
    show (2 : ℝ) ≤ 1 * 1 * 1 ^ 2 * 2 ^ 2 * (1 + 1) + 1 * 1 * 2 ^ 2 * 1
    norm_num
  i3 := by simp
  i4 := fun _ => by simp
  i5 := fun _ => by simp
  i6 := fun _ => ⟨le_refl _, by show (0 : ℝ) ≤ 2 ^ 2; norm_num⟩
  i7 := fun _ => by
    show Real.log (8 + 32 * ((Fintype.card (Fin 1) : ℝ) * 0) * 0) ≤ 1 * Real.log (8 * Real.exp 8 * 1)
    rw [La8]; simp
  i8 := fun _ _ => by
    show Real.log (2 * (∑ _i : Fin 1, (3 : ℝ)) + 2) ≤ 1 * Real.log (8 * Real.exp 8 * 1)
    rw [La8]
    have : (2 * (∑ _i : Fin 1, (3 : ℝ)) + 2) = 8 := by simp; norm_num
    rw [this]; linarith
  i9 := by show (1 : ℝ) ≤ 1 * 8; norm_num
  i10 := by norm_num
  t1 := by
    show (0 : ℝ) ≤ -(∑ _τ : Fin 1, (3 / 2 : ℝ) * 1) + (∑ _τ : Fin 1, (2 * (0 : ℝ) + 0)) + 2
    simp; norm_num
  t2 := fun _ => by simp
  t3 := fun _ => by
    show (0 : ℝ) ≤ 2 * (2 - 1) / 2 * Real.log (2 * (8 * Real.exp 8))
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (8 * Real.exp 8) by linarith [e8])
    linarith
  t4 := fun _ => by norm_num
  t5 := fun _ _ => by show (3 / 2 : ℝ) = 2 - (2 - 1) / 2; norm_num
  t6 := fun τ h => absurd (Finset.mem_univ τ) h
  t7 := fun _ => by simp [recNumsExample]
  t8 := fun _ => by simp [recNumsExample]
  t9 := fun _ _ => by show (0 : ℝ) ≤ 2 * 1; norm_num
  t10 := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℝ) ≤ 1; norm_num
    · show (1 : ℝ) ≤ 1 * 1 * 8; norm_num
    · norm_num
  t11 := by
    refine ⟨?_, by norm_num⟩
    show (2 : ℝ) ≤ 1 * 1 * 2 ^ 2 * Real.log (8 * Real.exp 8 * 1)
    rw [La8]; linarith [l8]
  k1 := by show 2 * (16 + 1 + 1) ≤ (36 : ℝ); norm_num
  k2 := by show (0 : ℝ) + 1 + 2 * 1 + 1 + 2 * 0 + 2 * 1 * 1 ≤ 36; norm_num
  k3 := by show 2 * ((1 : ℝ) + 0) * (1 + 1) ≤ 36; norm_num

theorem exampleHeightNumbers_size_nonneg (J : Type) [Fintype J] [Unique J] (ce : ℝ) (hce : 36 ≤ ce) (Emb : Type) [Fintype Emb] [Nonempty Emb]
    (j : J) (s : Emb) : 0 ≤ (exampleHeightNumbers J ce hce Emb).sz j s := by
  have : (exampleHeightNumbers J ce hce Emb).sz j s = ph 3 + 7 / 2 := by
    show (∑ _τ : Fin 1, ((∑ _i : Fin 1, ph 3) - (∑ _i : Fin 1, (3 : ℝ)) * (1 / 2))) + (Fintype.card (Fin 1) : ℝ) * 0 * 0 +
      ((Fintype.card (Fin 1) : ℝ) * 0 * Real.log (8 + 32 * ((Fintype.card (Fin 1) : ℝ) * 0) * 0) + 2 * 2 +
        (∑ _τ : Fin 1, (1 + 2 * (0 : ℝ) * Real.log (2 * (∑ _i : Fin 1, (3 : ℝ)) + 2))) + ((0 : ℝ) + 0)) = ph 3 + 7 / 2
    simp; ring
  rw [this]; linarith [neg_three_le_phi_three]

theorem recNumsExample_hX_nonpos (J : Type) [Fintype J] [Unique J] (ce : ℝ) (h : 36 ≤ ce) (j : J) : (recNumsExample J ce h).hX j ≤ 0 := by
  show (∑ _ρ : Fin 1, (ph 3 - ph 2)) - 36 * 1 * 1 ^ 2 * 1 ≤ 0
  rw [Fin.sum_univ_one]
  linarith [ph32]

theorem le_recNumsExample_errB (J : Type) [Fintype J] [Unique J] (t : ℝ) :
    t ≤ (recNumsExample J (36 + |t|) (by linarith [abs_nonneg t])).errB := by
  show t ≤ (36 + |t|) * 1 * ((8 : ℝ) ^ (1 : ℝ) * (1 * 1 * Real.exp 8 * (8 : ℝ) ^ (1 : ℝ) + 1))
  rw [Real.rpow_one]
  have he := Real.exp_pos 8
  have ha := abs_nonneg t
  have hle := le_abs_self t
  have h1 : (1 : ℝ) ≤ 8 * (1 * 1 * Real.exp 8 * 8 + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 36 + |t|)]

theorem sl_coord {K : Type} [Field K] [NumberField K] [StarRing K] (x : Fin 1 → K) (hx : x ∈ sl K 1) :
    ∃ r : 𝓞 K, x 0 = (r : K) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
  refine ⟨c 0, ?_⟩
  rw [← hc]
  simp [sb, Algebra.smul_def]

theorem toDual_one {K : Type} [Field K] (x y : Fin 1 → K) : (Pi.basisFun K (Fin 1)).toDual x y = x 0 * y 0 := by
  have hy : y = y 0 • (Pi.basisFun K (Fin 1)) 0 := by
    ext i
    fin_cases i
    simp
  conv_lhs => rw [hy]
  rw [map_smul, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, mul_comm]

theorem chain_one : chainMat (R := K3) (m := 1) (c := fun _ => 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) K3)) (Fin.last 1) = 1 := by
  show (1 : Matrix (Fin 1) (Fin 1) K3) * 1 = 1
  exact mul_one _

theorem norm_toDual (v : InfinitePlace K3) :
    Formalism.HN.opNormAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)).dualBasis
      (Formalism.HN.dualFrame (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))) v (Pi.basisFun K3 (Fin 1)).toDual ^ 2 ≤ Real.exp 0 := by
  have hM : (Formalism.HN.dualFrame (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) v)⁻¹ *
      (LinearMap.toMatrix (Pi.basisFun K3 (Fin 1)) (Pi.basisFun K3 (Fin 1)).dualBasis
        (Pi.basisFun K3 (Fin 1)).toDual).map v.embedding * fr K3 1 v = 1 := by
    ext i j; fin_cases i; fin_cases j
    simp [Formalism.HN.dualFrame, fr, LinearMap.toMatrix_apply, toDual_one]
  have h1 : Formalism.HN.opNormAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)).dualBasis
      (Formalism.HN.dualFrame (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))) v (Pi.basisFun K3 (Fin 1)).toDual ≤ 1 := by
    rw [Formalism.HN.opNormAt, hM]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp
  have h0 := OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)).dualBasis
      (Formalism.HN.dualFrame (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))) v (Pi.basisFun K3 (Fin 1)).toDual
  rw [Real.exp_zero]
  nlinarith

theorem norm_one (v : InfinitePlace K3) {t : ℝ} (ht : 0 ≤ t) :
    Formalism.HN.opNormAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)) (fr K3 1) v
      (Matrix.mulVecLin (1 : Matrix (Fin 1) (Fin 1) K3)) ^ 2 ≤ Real.exp t := by
  have hM : (fr K3 1 v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K3 (Fin 1)) (Pi.basisFun K3 (Fin 1))
        (Matrix.mulVecLin (1 : Matrix (Fin 1) (Fin 1) K3))).map v.embedding * fr K3 1 v = 1 := by
    ext i j; fin_cases i; fin_cases j
    simp [fr]
  have h1 : Formalism.HN.opNormAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)) (fr K3 1) v
      (Matrix.mulVecLin (1 : Matrix (Fin 1) (Fin 1) K3)) ≤ 1 := by
    rw [Formalism.HN.opNormAt, hM]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp
  have h0 := OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)) (fr K3 1) v
      (Matrix.mulVecLin (1 : Matrix (Fin 1) (Fin 1) K3))
  have h2 := Real.one_le_exp ht
  nlinarith

def chOne (v0 : InfinitePlace K3) : ColChain (one.dc K3 v0) () where
  mm := 1
  lf := fun _ => 0
  c := fun _ => 1
  c0 := rfl
  X := fun _ => fr K3 1
  X_unit := fun _ v => by simp [fr]
  X_zero := fun _ _ _ => rfl
  Kj := fun _ => (1 : Matrix (Fin 1) (Fin 1) K3)
  PtL := (Pi.basisFun K3 (Fin 1)).toDual
  fact := fun φ F => by
    show (Pi.basisFun K3 (Fin 1)).toDual φ F = (Pi.basisFun K3 (Fin 1)).toDual
      ((chainMat (R := K3) (m := 1) (c := fun _ => 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) K3)) (Fin.last 1)).mulVec φ) F
    rw [chain_one, Matrix.one_mulVec]

def chTwo (v0 : InfinitePlace K3) : ColChain (two.dc K3 v0 3) () where
  mm := 1
  lf := fun _ => 0
  c := fun _ => 1
  c0 := rfl
  X := fun _ => fr K3 1
  X_unit := fun _ v => by simp [fr]
  X_zero := fun _ _ _ => rfl
  Kj := fun _ => (1 : Matrix (Fin 1) (Fin 1) K3)
  PtL := (Pi.basisFun K3 (Fin 1)).toDual
  fact := fun φ F => by
    show (Pi.basisFun K3 (Fin 1)).toDual φ F = (Pi.basisFun K3 (Fin 1)).toDual
      ((chainMat (R := K3) (m := 1) (c := fun _ => 1) (fun _ => (1 : Matrix (Fin 1) (Fin 1) K3)) (Fin.last 1)).mulVec φ) F
    rw [chain_one, Matrix.one_mulVec]

def cbStd {m : ℕ} (Kj : ∀ _ : Fin m, Matrix (Fin 1) (Fin 1) K3) (ht : ∀ j (v : InfinitePlace K3), ‖v.embedding (Kj j 0 0)‖ ^ 2 ≤ 1) :
    CBData (c := fun _ => 1) (fun _ => fr K3 1) Kj where
  AA := fun _ => Fin 1
  Cl := fun _ _ => Unit
  W := fun _ _ => ℂ
  γ := fun _ _ => 1
  Φ := fun _ _ x p => x p.1
  ε := fun _ _ _ _ => 1
  T := fun j v p q => (v.embedding (Kj j q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ
  hcl := fun _ => 1
  tmax := fun _ _ => 1
  hyp := Formalism.DimensionVariation.cbHyp_matrix K3 m (fun _ => 1) Kj (fun _ _ => 1) (fun _ _ => zero_le_one)
    (fun j v q p => by rw [Subsingleton.elim q 0, Subsingleton.elim p 0]; exact ht j v)

theorem cbStd_sq {m : ℕ} (Kj : ∀ _ : Fin m, Matrix (Fin 1) (Fin 1) K3) (ht : ∀ j (v : InfinitePlace K3), ‖v.embedding (Kj j 0 0)‖ ^ 2 ≤ 1)
    (j : Fin m) (v : InfinitePlace K3) : (cbStd Kj ht).sq j v = 1 := by
  have hc : ∀ inst : Fintype (Fin 1), @Fintype.card (Fin 1) inst = 1 := fun inst => by convert Fintype.card_fin 1
  show Formalism.DimensionVariation.cbSq (@Fintype.card (Fin 1) _) (@Fintype.card (Fin 1) _) 1 1 1 = 1
  rw [hc]
  norm_num [Formalism.DimensionVariation.cbSq]

theorem one_entry (v : InfinitePlace K3) : ‖v.embedding ((1 : Matrix (Fin 1) (Fin 1) K3) 0 0)‖ ^ 2 ≤ 1 := by
  simp

def tOne : ℝ := lcv (fr K3 1) (sl K3 1) / ((1 : ℕ) : ℝ)

def recOne : RecNums Unit (Fin 1) := recNumsExample Unit (36 + |tOne|) (by linarith [abs_nonneg tOne])

def exampleDivisionInputs (v0 : InfinitePlace K3) : DivInputs (coreOne v0) recOne () (sl K3 1) (fun _ => 0) where
  Nu_lat := sl_lattice K3 1
  sg_fin := by
    have h : shiftZ (K := K3) (fun _ => (0 : ℝ)) = 0 := by funext w; simp [shiftZ]
    rw [h, Function.support_zero]; exact Set.finite_empty
  val2 := fun w φ hφ F hF => by
    right
    obtain ⟨r, hr⟩ := sl_coord φ hφ
    obtain ⟨s, hs⟩ := sl_coord F hF
    show ((0 : ℝ)) ≤ (vw w ((Pi.basisFun K3 (Fin 1)).toDual φ F) : ℝ)
    rw [toDual_one, hr, hs, ← map_mul]
    exact_mod_cast ValuationRepresentative.vw_int_nonneg w (r * s)
  Xc_unit := fun v => by simp [fr]
  a_pos := one_pos
  X0 := fun _ => 1
  base_matrix_det_unit := fun v => ⟨by simp, by simp [Matrix.map_one]⟩
  ch := chOne v0
  hn := exampleHeightNumbers Unit _ _ _
  nP := fun v => norm_toDual v
  cb := cbStd (m := 1) (fun _ => 1) (fun _ v => one_entry v)
  nKcb := fun _ v => by
    have h : ∀ t : ℝ, t = 1 → Real.log t = 0 := fun t ht => by rw [ht, Real.log_one]
    refine (h _ ?_).trans_le (Finset.sum_nonneg fun _ _ => exampleHeightNumbers_size_nonneg _ _ _ _ _ _)
    exact cbStd_sq _ _ _ _
  eig6 := by
    show ∑ j : Unit, recOne.hX j ≤ ∑ _j : Unit, (0 : ℝ)
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact recNumsExample_hX_nonpos _ _ _ _
  eb := fun _ _ => sb K3 1
  heb := fun _ w => by
    show IsLocBasis (matLat (1 : Matrix (Fin 1) (Fin 1) K3) (sl K3 1)) w (sb K3 1)
    rw [Examples₂.matLat_one]; exact locB K3 1 w
  Sy := ∅
  Sy_tw := fun _ h => h
  G0 := fun y _ => by
    show vw y (gramR (quotGram (1 : Matrix (Fin 1) (Fin 1) K3) 1) (sb K3 1)) = 0
    simp [quotGram, gramR_one, ValuationRepresentative.vw_one]
  LG := 0
  E3 := 0
  E2 := fun _ => 0
  gy := fun _ => 0
  ηy := fun _ _ => 0
  bi := fun y h => absurd h (Finset.notMem_empty y)
  bLG := by simp
  biv := fun y h => absurd h (Finset.notMem_empty y)
  borderedMinorImage := fun _ => by simp
  twisted_third_sum_le := by simp
  El3 := tOne
  L3main := by
    show ∑ _j : Unit, tOne ≤ (∑ _j : Unit, ∑ _ρ : Fin 1, (1 : ℝ) * 1 * (1 / 2)) + tOne
    simp
  errB := by
    show tOne + 0 + (∑ _j : Unit, ((0 : ℝ) + 0)) + 0 ≤ recOne.errB
    simp only [Finset.univ_unique, Finset.sum_singleton, add_zero]
    exact le_recNumsExample_errB Unit tOne
  Q := 1 + |boundB (coreOne v0) 0 0 (fun _ => 0) + (one.num K3 v0).hh + 28 * (one.num K3 v0).la|
  de0 := by show (0 : ℝ) ≤ 0; exact le_refl _
  deQ := by show 3 * (0 : ℝ) * _ ≤ 1; simp
  Q1 := by linarith [abs_nonneg (boundB (coreOne v0) 0 0 (fun _ => 0) + (one.num K3 v0).hh + 28 * (one.num K3 v0).la)]
  Qb := by linarith [le_abs_self (boundB (coreOne v0) 0 0 (fun _ => 0) + (one.num K3 v0).hh + 28 * (one.num K3 v0).la)]
  la_le := by show (0 : ℝ) ≤ 1; norm_num
  constant_ge_twenty_eight := by show (28 : ℝ) ≤ 36; norm_num

theorem toyCoreOne_divClauses (v0 : InfinitePlace K3) : DivClauses (coreOne v0) recOne () (sl K3 1) (fun _ => 0) :=
  divClauses_of (one.wf K3 v0 (conjAt v0)) (one.wf K3 v0 (conjAt v0)) (coreOne v0) _ () _ _ (exampleDivisionInputs v0)

def tTwo (w : HeightOneSpectrum (𝓞 K3)) : ℝ :=
  lcv (scaleFrame (fun _ => (5 : ℝ)) (fr K3 1)) (sl K3 1) / ((1 : ℕ) : ℝ) + ∑ y ∈ pairSet w, lw y * (2 / ellw y ^ 2)

def recTwo (w : HeightOneSpectrum (𝓞 K3)) : RecNums Unit (Fin 1) :=
  recNumsExample Unit (36 + |tTwo w|) (by linarith [abs_nonneg (tTwo w)])

theorem two_val (w : HeightOneSpectrum (𝓞 K3)) (t : Bool) (φ F : Fin 1 → K3) (hφ : φ ∈ sl K3 1) (hF : F ∈ sl K3 1) :
    0 ≤ vw w ((cond t ((3 : K3) • (Pi.basisFun K3 (Fin 1)).toDual) (Pi.basisFun K3 (Fin 1)).toDual) φ F) := by
  obtain ⟨r, hr⟩ := sl_coord φ hφ
  obtain ⟨s, hs⟩ := sl_coord F hF
  cases t
  · simp only [cond_false]
    rw [toDual_one, hr, hs, ← map_mul]
    exact ValuationRepresentative.vw_int_nonneg w (r * s)
  · simp only [cond_true, LinearMap.smul_apply, toDual_one, hr, hs, smul_eq_mul]
    have : (3 : K3) * ((r : K3) * (s : K3)) = ((r * s + r * s + r * s : 𝓞 K3) : K3) := by push_cast; ring
    rw [this]
    exact ValuationRepresentative.vw_int_nonneg w (r * s + r * s + r * s)

open scoped Classical in

def inpTwoOf (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) (sg : HeightOneSpectrum (𝓞 K3) → ℝ)
    (hfin : (Function.support (shiftZ sg)).Finite)
    (hval : ∀ y, ∀ φ ∈ sl K3 1, ∀ F ∈ sl K3 1,
      (cond (decide (y ∈ pairSet w)) ((3 : K3) • (Pi.basisFun K3 (Fin 1)).toDual) (Pi.basisFun K3 (Fin 1)).toDual) φ F = 0 ∨
      sg y ≤ (vw y ((cond (decide (y ∈ pairSet w)) ((3 : K3) • (Pi.basisFun K3 (Fin 1)).toDual)
        (Pi.basisFun K3 (Fin 1)).toDual) φ F) : ℝ)) :
    DivInputs (coreTwo v0 w) (recTwo w) () (sl K3 1) sg where
  Nu_lat := sl_lattice K3 1
  sg_fin := hfin
  val2 := hval
  Xc_unit := fun v => by simp [fr]
  a_pos := one_pos
  X0 := fun _ => 1
  base_matrix_det_unit := fun v => ⟨by simp, by simp [Matrix.map_one]⟩
  ch := chTwo v0
  hn := exampleHeightNumbers Unit _ _ _
  nP := fun v => norm_toDual v
  cb := cbStd (m := 1) (fun _ => 1) (fun _ v => one_entry v)
  nKcb := fun _ v => by
    have h : ∀ t : ℝ, t = 1 → Real.log t = 0 := fun t ht => by rw [ht, Real.log_one]
    refine (h _ ?_).trans_le (Finset.sum_nonneg fun _ _ => exampleHeightNumbers_size_nonneg _ _ _ _ _ _)
    exact cbStd_sq _ _ _ _
  eig6 := by
    show ∑ j : Unit, (recTwo w).hX j ≤
      ∑ _j : Unit, Finset.univ.inf' Finset.univ_nonempty fun v : InfinitePlace K3 => Real.log ((fun _ => (5 : ℝ)) v)
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact (recNumsExample_hX_nonpos _ _ _ _).trans (Finset.le_inf' _ _ fun v _ => Real.log_nonneg (by norm_num))
  eb := fun _ _ => sb K3 1
  heb := fun _ y => by
    show IsLocBasis (matLat (1 : Matrix (Fin 1) (Fin 1) K3) (sl K3 1)) y (sb K3 1)
    rw [Examples₂.matLat_one]; exact locB K3 1 y
  Sy := pairSet w
  Sy_tw := fun _ h => h
  G0 := fun y _ => by
    show vw y (gramR (quotGram (1 : Matrix (Fin 1) (Fin 1) K3) 1) (sb K3 1)) = 0
    simp [quotGram, gramR_one, ValuationRepresentative.vw_one]
  LG := 0
  E3 := ∑ y ∈ pairSet w, lw y * (2 / ellw y ^ 2)
  E2 := fun _ => 0
  gy := fun _ => 0
  ηy := fun _ _ => 0
  bi := fun y _ => by
    show (vw y (gramR (quotGram (1 : Matrix (Fin 1) (Fin 1) K3) 1) (sb K3 1)) : ℝ) ≤ ((1 : ℕ) : ℝ) * 0
    simp [quotGram, gramR_one, ValuationRepresentative.vw_one]
  bLG := by simp
  biv := fun y _ _ => by
    show (jw (1 : Matrix (Fin 1) (Fin 1) K3) y (sl K3 1) : ℝ) ≤ ((ramw y : ℝ) * 0) * ((1 : ℕ) : ℝ) + 0
    rw [jw_std]; simp
  borderedMinorImage := fun _ => by simp
  twisted_third_sum_le := le_refl _
  El3 := lcv (scaleFrame (fun _ => (5 : ℝ)) (fr K3 1)) (sl K3 1) / ((1 : ℕ) : ℝ)
  L3main := by
    show ∑ _j : Unit, lcv (scaleFrame (fun _ => (5 : ℝ)) (fr K3 1)) (sl K3 1) / ((1 : ℕ) : ℝ) ≤
      (∑ _j : Unit, ∑ _ρ : Fin 1, (1 : ℝ) * 1 * (1 / 2)) + lcv (scaleFrame (fun _ => (5 : ℝ)) (fr K3 1)) (sl K3 1) / ((1 : ℕ) : ℝ)
    simp
  errB := by
    show lcv (scaleFrame (fun _ => (5 : ℝ)) (fr K3 1)) (sl K3 1) / ((1 : ℕ) : ℝ) + 0 + (∑ _j : Unit, ((0 : ℝ) + 0)) +
      ∑ y ∈ pairSet w, lw y * (2 / ellw y ^ 2) ≤ (recTwo w).errB
    simp only [Finset.univ_unique, Finset.sum_singleton, add_zero]
    exact le_recNumsExample_errB Unit (tTwo w)
  Q := 1 + |boundB (coreTwo v0 w) 0 (∑ y ∈ pairSet w, lw y * (2 / ellw y ^ 2)) (fun _ => 0) +
    (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)).hh + 28 * (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)).la|
  de0 := by show (0 : ℝ) ≤ 0; exact le_refl _
  deQ := by show 3 * (0 : ℝ) * _ ≤ 1; simp
  Q1 := by linarith [abs_nonneg (boundB (coreTwo v0 w) 0 (∑ y ∈ pairSet w, lw y * (2 / ellw y ^ 2)) (fun _ => 0) +
    (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)).hh + 28 * (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)).la)]
  Qb := by linarith [le_abs_self (boundB (coreTwo v0 w) 0 (∑ y ∈ pairSet w, lw y * (2 / ellw y ^ 2)) (fun _ => 0) +
    (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)).hh + 28 * (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)).la)]
  la_le := by show (0 : ℝ) ≤ 1; norm_num
  constant_ge_twenty_eight := by show (28 : ℝ) ≤ 36; norm_num

open scoped Classical in

def inpTwo (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) :
    DivInputs (coreTwo v0 w) (recTwo w) () (sl K3 1) (fun _ => 0) :=
  inpTwoOf v0 w (fun _ => 0)
    (by
      have h : shiftZ (K := K3) (fun _ => (0 : ℝ)) = 0 := by funext w; simp [shiftZ]
      rw [h, Function.support_zero]; exact Set.finite_empty)
    (fun y φ hφ F hF => by
      right
      have h := two_val y (decide (y ∈ pairSet w)) φ F hφ hF
      exact_mod_cast h)

theorem clauses_two (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) :
    DivClauses (coreTwo v0 w) (recTwo w) () (sl K3 1) (fun _ => 0) :=
  divClauses_of (two.wf K3 v0 (conjAt v0)) (two.wf K3 v0 (conjAt v0)) (coreTwo v0 w) _ () _ _ (inpTwo v0 w)

open scoped Classical in

def sgf (w : HeightOneSpectrum (𝓞 K3)) (y : HeightOneSpectrum (𝓞 K3)) : ℝ :=
  if y ∈ pairSet w then 1 else 0

theorem vw3 (y : HeightOneSpectrum (𝓞 K3)) (h : ((3 : ℕ) : 𝓞 K3) ∈ y.asIdeal) : 1 ≤ vw y ((3 : ℕ) : K3) := by
  have := ((Formalism.DivisionValues.lwSumPrime K3 3 Nat.prime_three).2.2.1 y).1 h
  omega

open scoped Classical in

def inpShift (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3))
    (h3 : ∀ y ∈ pairSet w, ((3 : ℕ) : 𝓞 K3) ∈ y.asIdeal) :
    DivInputs (coreTwo v0 w) (recTwo w) () (sl K3 1) (sgf w) :=
  inpTwoOf v0 w (sgf w)
    (by
      apply (pairSet w).finite_toSet.subset
      intro y hy
      by_contra hn
      apply hy
      simp [shiftZ, sgf, show y ∉ pairSet w from hn])
    (fun y φ hφ F hF => by
      obtain ⟨r, hr⟩ := sl_coord φ hφ
      obtain ⟨s, hs⟩ := sl_coord F hF
      by_cases hy : y ∈ pairSet w
      · simp only [hy, decide_true, cond_true, LinearMap.smul_apply, smul_eq_mul, sgf, if_true]
        rw [toDual_one, hr, hs]
        by_cases h0 : ((r : K3) * (s : K3)) = 0
        · left; rw [h0, mul_zero]
        · right
          have h3' : (3 : K3) ≠ 0 := by norm_num
          rw [ValuationRepresentative.vw_mul y 3 _ h3' h0]
          have ha : 1 ≤ vw y (3 : K3) := by
            have := vw3 y (h3 y hy); simpa using this
          have hb : 0 ≤ vw y ((r : K3) * (s : K3)) := by
            rw [← map_mul]; exact ValuationRepresentative.vw_int_nonneg y (r * s)
          exact_mod_cast (by omega : (1 : ℤ) ≤ vw y 3 + vw y ((r : K3) * (s : K3)))
      · right
        have h := two_val y (decide (y ∈ pairSet w)) φ F hφ hF
        rw [show sgf w y = 0 by simp [sgf, hy]]
        exact_mod_cast h)

theorem third_hypothesis_of_params (w : HeightOneSpectrum (𝓞 K3)) (h : ((3 : ℕ) : 𝓞 K3) ∈ w.asIdeal) :
    ∀ y ∈ pairSet w, ((3 : ℕ) : 𝓞 K3) ∈ y.asIdeal := by
  intro y hy
  simp only [pairSet, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact h
  · show ((3 : ℕ) : 𝓞 K3) ∈ w.asIdeal.map (cO K3)
    have := Ideal.mem_map_of_mem (cO K3) h
    rwa [map_natCast] at this

theorem clauses_shift (v0 : InfinitePlace K3) : ∃ w : HeightOneSpectrum (𝓞 K3),
    DivClauses (coreTwo v0 w) (recTwo w) () (sl K3 1) (sgf w) ∧ ∀ y ∈ pairSet w, shiftZ (sgf w) y = 1 := by
  obtain ⟨w, hw⟩ := (Formalism.DivisionValues.lwSumPrime K3 3 Nat.prime_three).2.1
  refine ⟨w, divClauses_of (two.wf K3 v0 (conjAt v0)) (two.wf K3 v0 (conjAt v0)) (coreTwo v0 w) _ () _ _
    (inpShift v0 w (third_hypothesis_of_params w hw)), fun y hy => ?_⟩
  simp [shiftZ, sgf, hy]

theorem coreTwo_B_ne_zero (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) : (coreTwo v0 w).cols.col.B () ≠ 0 := by
  intro h
  have := congrArg (fun B : (Fin 1 → K3) →ₗ[K3] Module.Dual K3 (Fin 1 → K3) => B (fun _ => 1) (fun _ => 1)) h
  change (Pi.basisFun K3 (Fin 1)).toDual (fun _ => 1) (fun _ => 1) = 0 at this
  rw [toDual_one] at this
  simp at this

theorem norm_smul_one (v : InfinitePlace K3) (a : K3) {t : ℝ} (ht : ‖v.embedding a‖ ^ 2 ≤ Real.exp t) :
    Formalism.HN.opNormAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)) (fr K3 1) v
      (Matrix.mulVecLin (a • (1 : Matrix (Fin 1) (Fin 1) K3))) ^ 2 ≤ Real.exp t := by
  have hM : (fr K3 1 v)⁻¹ * (LinearMap.toMatrix (Pi.basisFun K3 (Fin 1)) (Pi.basisFun K3 (Fin 1))
        (Matrix.mulVecLin (a • (1 : Matrix (Fin 1) (Fin 1) K3)))).map v.embedding * fr K3 1 v =
      (v.embedding a) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j
    simp [fr]
  have h1 : Formalism.HN.opNormAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)) (fr K3 1) v
      (Matrix.mulVecLin (a • (1 : Matrix (Fin 1) (Fin 1) K3))) ≤ ‖v.embedding a‖ := by
    rw [Formalism.HN.opNormAt, hM]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    simp [norm_smul]
  have h0 := OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)) (fr K3 1) v
      (Matrix.mulVecLin (a • (1 : Matrix (Fin 1) (Fin 1) K3)))
  exact (pow_le_pow_left₀ h0 h1 2).trans ht

def kk : Fin 2 → K3 := ![2, 2⁻¹]

theorem chain_two : chainMat (R := K3) (m := 2) (c := fun _ => 1) (fun j => kk j • (1 : Matrix (Fin 1) (Fin 1) K3)) (Fin.last 2) = 1 := by
  show (kk 1 • (1 : Matrix (Fin 1) (Fin 1) K3)) * ((kk 0 • (1 : Matrix (Fin 1) (Fin 1) K3)) * 1) = 1
  have h : kk 1 * kk 0 = 1 := by
    show (2 : K3)⁻¹ * 2 = 1
    exact inv_mul_cancel₀ two_ne_zero
  rw [mul_one, Matrix.smul_mul, one_mul, smul_smul, h, one_smul]

def chThree (v0 : InfinitePlace K3) : ColChain (three.dc K3 v0) () where
  mm := 2
  lf := fun l => l
  c := fun _ => 1
  c0 := rfl
  X := fun _ => fr K3 1
  X_unit := fun _ v => by simp [fr]
  X_zero := fun _ _ _ => rfl
  Kj := fun j => kk j • (1 : Matrix (Fin 1) (Fin 1) K3)
  PtL := (Pi.basisFun K3 (Fin 1)).toDual
  fact := fun φ F => by
    show (Pi.basisFun K3 (Fin 1)).toDual φ F = (Pi.basisFun K3 (Fin 1)).toDual
      ((chainMat (R := K3) (m := 2) (c := fun _ => 1) (fun j => kk j • (1 : Matrix (Fin 1) (Fin 1) K3)) (Fin.last 2)).mulVec φ) F
    rw [chain_two, Matrix.one_mulVec]

theorem fiber_id {n : ℕ} (f : Fin n → ℝ) (j : Fin n) : ∑ l ∈ Finset.univ.filter (fun l => l = j), f l = f j := by
  simp [Finset.filter_eq']

theorem height_three (v0 : InfinitePlace K3) :
    Formalism.HN.htMap (Pi.basisFun K3 (Fin 1)) (fr K3 1) (Pi.basisFun K3 (Fin 1)).dualBasis
              (Formalism.HN.dualFrame (three.core (K := K3) (v0 := v0) (kap := 3) (by norm_num) example_weights_pos).cols.XE)
              ((three.core (K := K3) (v0 := v0) (kap := 3) (by norm_num) example_weights_pos).cols.col.B ()) ≤
      0 + ∑ j : Fin 2, (∑ _v : InfinitePlace K3, (![2, -1] : Fin 2 → ℝ) j) / (Fintype.card (InfinitePlace K3) : ℝ) -
        ∑ j, (three.num K3 v0 3 l4).l6 j - meanLog (three.core (K := K3) (v0 := v0) (kap := 3) (by norm_num) example_weights_pos).cols.κ := by
  have : Nonempty (three.base K3 v0).Ix := ⟨(0 : Fin 2)⟩
  refine height_chain (three.wf1 K3 v0 (conjAt v0)) (three.core (K := K3) (v0 := v0) (kap := 3) (by norm_num) example_weights_pos).cols ()
    ?_ (fun _ => 1) (fun v => ⟨by simp, by simp [Matrix.map_one]⟩) (chThree v0) 0 (fun j _ => (![2, -1] : Fin 2 → ℝ) j)
    (fun v => norm_toDual v) (fun j v => ?_)
  · intro h
    have := congrArg (fun B : (Fin 1 → K3) →ₗ[K3] Module.Dual K3 (Fin 1 → K3) => B (fun _ => 1) (fun _ => 1)) h
    change (Pi.basisFun K3 (Fin 1)).toDual (fun _ => 1) (fun _ => 1) = 0 at this
    rw [toDual_one] at this
    simp at this
  · refine le_of_le_of_eq (norm_smul_one v (kk j) (t := (![2, -1] : Fin 2 → ℝ) j) ?_) ?_
    swap
    · congr 1
      exact (fiber_id (fun l => (![2, -1] : Fin 2 → ℝ) l) j).symm
    fin_cases j
    · show ‖v.embedding (2 : K3)‖ ^ 2 ≤ Real.exp 2
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      simp only [map_ofNat]
      norm_num
      linarith
    · show ‖v.embedding ((2 : K3)⁻¹)‖ ^ 2 ≤ Real.exp (-1)
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
      have h3 : (1 / 4 : ℝ) ≤ (Real.exp 1)⁻¹ := by
        rw [one_div]; exact inv_anti₀ (Real.exp_pos 1) (by linarith)
      rw [h2, map_inv₀, map_ofNat]
      norm_num
      linarith

abbrev pt : Formalism.L2.Col.GSD K3 := Formalism.L2.Col.GSD.triv K3 Unit Unit

theorem pt_ok : pt.Ok := Formalism.L2.Col.GSD.triv_ok K3 Unit Unit inferInstance (fun _ => inferInstance)

instance cl_unique (S : Formalism.L2.Col.GSD K3) [Unique S.D] : Unique S.Cl where
  default := S.cls default
  uniq a := Quotient.inductionOn a fun x => by rw [Subsingleton.elim x default]; rfl

theorem wt_one (S : Formalism.L2.Col.GSD K3) [Subsingleton S.G] (h : S.Ok) (s : S.Sec) (c : S.Cl) : (S.toCSDOf h s).wt c = 1 := by
  show @Fintype.card _ ((S.toCSDOf h s).finGam c) = 1
  exact (@Fintype.card_eq_one_iff _ ((S.toCSDOf h s).finGam c)).2 ⟨1, fun x => Subtype.ext (Subsingleton.elim _ _)⟩

abbrev ptY : Formalism.L2.Col.Cpl pt where
  Yb := Unit
  ys _ := Set.univ
  fin _ := Set.finite_univ
  equiv _ _ _ := Iff.rfl

def sK (a : K3) : Formalism.L2.Col.ClsKer pt pt := ⟨fun _ _ => a • LinearMap.id, fun _ _ _ _ => LinearMap.ext fun _ => rfl⟩

def cK (a b : K3) : Formalism.L2.Col.CplKer pt pt pt ptY :=
  ⟨fun _ _ _ => a • LinearMap.id, fun _ _ _ => b • LinearMap.id, fun _ _ _ _ _ => LinearMap.ext fun _ => rfl,
    fun _ _ _ _ _ => LinearMap.ext fun _ => rfl⟩

abbrev ptQ (n : ℕ) (a : ℕ → K3) (b1 b2 : K3) : KerChain K3 where
  n := n
  F := fun _ => pt.toFam
  hF := fun _ _ => pt_ok
  kk := fun j _ _ => sK (a j)
  S := pt
  hS := pt_ok
  S₁ := pt
  hS₁ := pt_ok
  Y := ptY
  cp := fun _ => cK b1 b2

def ptIn : (Fin 1 → K3) →ₗ[K3] pt.EqFun :=
  LinearMap.codRestrict pt.EqFun (LinearMap.pi fun _ => LinearMap.proj 0) (fun _ _ _ => rfl)

theorem ptIn_apply (x : Fin 1 → K3) (d : Unit) : (ptIn x : Unit → K3) d = x 0 := rfl

def ptInF : (Fin 1 → K3) →ₗ[K3] pt.toFam.Forms := LinearMap.pi fun _ => ptIn

theorem ptInF_apply (x : Fin 1 → K3) (b : Unit) : ptInF x b = ptIn x := rfl

theorem sK_opOf (a : K3) (h : pt.Ok) (s : pt.Sec) (x : Fin 1 → K3) : (sK a).opOf h s (ptIn x) = ptIn (a • x) := by
  apply Subtype.ext
  funext d
  show (Formalism.L2.Col.ClsKer.appOf (sK a) h s (ptIn x : Unit → K3) d) = (ptIn (a • x) : Unit → K3) d
  simp only [Formalism.L2.Col.ClsKer.appOf, Finset.univ_unique, Finset.sum_singleton, wt_one, Nat.cast_one, inv_one, one_smul]
  rfl

theorem cK_opOf (a b : K3) (h : pt.Ok) (s : pt.Sec) (x : Fin 1 → K3) :
    ((cK a b).comp pt_ok pt.outSec).opOf h s (ptIn x) = ptIn ((b * a) • x) := by
  apply Subtype.ext
  funext d
  show (Formalism.L2.Col.ClsKer.appOf ((cK a b).comp pt_ok pt.outSec) h s (ptIn x : Unit → K3) d) = (ptIn ((b * a) • x) : Unit → K3) d
  simp only [Formalism.L2.Col.ClsKer.appOf, Formalism.L2.Col.CplKer.comp, Finset.univ_unique, Finset.sum_singleton, wt_one, Nat.cast_one,
    inv_one, one_smul]
  rw [LinearMap.sum_apply, Finset.sum_eq_single_of_mem () (by simp) (fun y _ hy => absurd (Subsingleton.elim y ()) hy)]
  simp only [cK, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  show b • a • x 0 = ((b * a) • x) 0
  rw [Pi.smul_apply, mul_smul]

theorem pt_step (n : ℕ) (a : ℕ → K3) (b1 b2 : K3) (j : ℕ) (x : Fin 1 → K3) :
    (ptQ n a b1 b2).step j (ptInF x) = ptInF (a j • x) := by
  funext b
  simp only [KerChain.step, Formalism.L2.Col.KerFam.step, Formalism.L2.Col.GFam.Mat.opOf, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Finset.univ_unique, Finset.sum_singleton, ptInF_apply]
  exact sK_opOf (a j) pt_ok pt.outSec x

theorem pt_cpl (n : ℕ) (a : ℕ → K3) (b1 b2 : K3) (x : Fin 1 → K3) :
    (ptQ n a b1 b2).cpl (ptInF x) = ptIn ((b2 * b1) • x) := by
  simp only [KerChain.cpl, LinearMap.comp_apply, LinearMap.proj_apply, Finset.univ_unique,
    Finset.sum_singleton, ptInF_apply]
  exact cK_opOf b1 b2 pt_ok pt.outSec x

theorem pt_ipAt (h : pt.Ok) (v : InfinitePlace K3) (x : Fin 1 → K3) :
    pt.ipAt h v (ptIn x : Unit → K3) (ptIn x : Unit → K3) = ((‖v.embedding (x 0)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Formalism.L2.Col.GSD.ipAt, Formalism.L2.Col.GSD.pairAt, Finset.univ_unique, Finset.sum_singleton]
  simp [wt_one, Formalism.L2.Col.GSD.gramV, Formalism.L2.DIV.CSD.pairOne, Complex.conj_mul']
  rfl

theorem fr_normAt (v : InfinitePlace K3) (x : Fin 1 → K3) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K3 (Fin 1)) (fr K3 1) v x ^ 2 : ℝ) : ℂ) = ((‖v.embedding (x 0)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, fr]

theorem pt_famIpAt (v : InfinitePlace K3) (x : Fin 1 → K3) :
    famIpAt pt.toFam (fun _ => pt_ok) v (ptInF x) (ptInF x) = ((‖v.embedding (x 0)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [famIpAt, Finset.univ_unique, Finset.sum_singleton, ptInF_apply]
  exact pt_ipAt pt_ok v x

def tieOne (v0 : InfinitePlace K3) : ChainTie (chOne v0) (ptQ 0 (fun _ => 1) 1 1) where
  hmm := rfl
  coF := fun _ _ => ptInF
  coL := ptIn
  metF := fun _ _ v x => (fr_normAt v x).trans (pt_famIpAt v x).symm
  metL := fun v x => (fr_normAt v x).trans (pt_ipAt pt_ok v x).symm
  kerF := fun j h _ => absurd h (Nat.not_lt_zero j)
  kerC := fun x => by
    have h1 := pt_cpl 0 (fun _ => 1) 1 1 x
    have h2 : ∀ y : Fin 1 → K3, (1 : Matrix (Fin 1) (Fin 1) K3).mulVec y = ((1 : K3) * 1) • y := fun y => by
      rw [Matrix.one_mulVec, mul_one, one_smul]
    exact (congrArg ptIn (h2 x)).trans h1.symm

def tieThree (v0 : InfinitePlace K3) : ChainTie (chThree v0) (ptQ 1 (fun _ => 2) 2⁻¹ 1) where
  hmm := rfl
  coF := fun _ _ => ptInF
  coL := ptIn
  metF := fun _ _ v x => (fr_normAt v x).trans (pt_famIpAt v x).symm
  metL := fun v x => (fr_normAt v x).trans (pt_ipAt pt_ok v x).symm
  kerF := fun j h x => by
    have hn : (ptQ 1 (fun _ => (2 : K3)) 2⁻¹ 1).n = 1 := rfl
    have hj : j = 0 := by omega
    subst hj
    have h1 := pt_step 1 (fun _ => 2) 2⁻¹ 1 0 x
    have h2 : ∀ y : Fin 1 → K3, (kk ⟨0, by omega⟩ • (1 : Matrix (Fin 1) (Fin 1) K3)).mulVec y = (2 : K3) • y := fun y => by
      rw [smul_one_mulVec]; rfl
    exact (congrArg ptInF (h2 x)).trans h1.symm
  kerC := fun x => by
    have h1 := pt_cpl 1 (fun _ => 2) 2⁻¹ 1 x
    have h2 : ∀ y : Fin 1 → K3, (kk ⟨1, by omega⟩ • (1 : Matrix (Fin 1) (Fin 1) K3)).mulVec y = ((1 : K3) * 2⁻¹) • y :=
      fun y => by rw [smul_one_mulVec, one_mul]; rfl
    exact (congrArg ptIn (h2 x)).trans h1.symm

theorem tieThree_chain (v0 : InfinitePlace K3) (x : Fin 1 → K3) :
    (tieThree v0).coL ((chainMat (chThree v0).Kj ⟨2, by show 2 < 2 + 1; omega⟩).mulVec x) =
      (ptQ 1 (fun _ => 2) 2⁻¹ 1).col (ptInF x) := (tieThree v0).chain x

theorem ptInF_eta (φ : pt.toFam.Forms) : φ = ptInF (fun _ => (φ () : Unit → K3) ()) := by
  funext b
  cases b
  exact Subtype.ext (funext fun d => by cases d; rfl)

theorem not_tied_two (v0 : InfinitePlace K3) : IsEmpty (ChainTie (chOne v0) (ptQ 0 (fun _ => 1) 2 1)) := by
  refine ⟨fun T => ?_⟩
  let one : Fin 1 → K3 := fun _ => 1
  let y : Fin 1 → K3 := fun _ => (T.coF 0 le_rfl one () : Unit → K3) ()
  have e1 : T.coF 0 le_rfl one = ptInF y := ptInF_eta _
  have hC : T.coL ((1 : Matrix (Fin 1) (Fin 1) K3).mulVec one) = ptIn (((1 : K3) * 2) • y) :=
    (T.kerC one).trans ((congrArg (ptQ 0 (fun _ => 1) 2 1).cpl e1).trans (pt_cpl 0 (fun _ => 1) 2 1 y))
  have hL : ((‖v0.embedding (((1 : Matrix (Fin 1) (Fin 1) K3).mulVec one) 0)‖ ^ 2 : ℝ) : ℂ) =
      ((‖v0.embedding ((((1 : K3) * 2) • y) 0)‖ ^ 2 : ℝ) : ℂ) := by
    have h := T.metL v0 ((1 : Matrix (Fin 1) (Fin 1) K3).mulVec one)
    rw [hC] at h
    exact (fr_normAt v0 _).symm.trans (h.trans (pt_ipAt pt_ok v0 _))
  have hF : ((‖v0.embedding (one 0)‖ ^ 2 : ℝ) : ℂ) = ((‖v0.embedding (y 0)‖ ^ 2 : ℝ) : ℂ) := by
    have h := T.metF 0 le_rfl v0 one
    rw [e1] at h
    exact (fr_normAt v0 _).symm.trans (h.trans (pt_famIpAt v0 y))
  have hL' := Complex.ofReal_injective hL
  have hF' := Complex.ofReal_injective hF
  have h1 : ‖v0.embedding (((1 : Matrix (Fin 1) (Fin 1) K3).mulVec one) 0)‖ = 1 := by simp [Matrix.one_mulVec, one]
  have h2 : ‖v0.embedding ((((1 : K3) * 2) • y) 0)‖ = 2 * ‖v0.embedding (y 0)‖ := by
    rw [Pi.smul_apply, smul_eq_mul, one_mul, map_mul, norm_mul, map_ofNat]
    norm_num
  have h3 : ‖v0.embedding (one 0)‖ = 1 := by simp [one]
  rw [h1, h2] at hL'
  rw [h3] at hF'
  nlinarith

theorem chOne_isom (v0 : InfinitePlace K3) :
    ∀ (v : InfinitePlace K3) (x : Fin ((chOne v0).c ⟨0, by omega⟩) → K3),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K3 (Fin ((chOne v0).c ⟨(ptQ 0 (fun _ => 1) 1 1).n + 1, by show 0 + 1 < 1 + 1; omega⟩)))
                ((chOne v0).X ⟨(ptQ 0 (fun _ => 1) 1 1).n + 1, by show 0 + 1 < 1 + 1; omega⟩) v
                ((chainMat (chOne v0).Kj ⟨(ptQ 0 (fun _ => 1) 1 1).n + 1, by show 0 + 1 < 1 + 1; omega⟩).mulVec x) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K3 (Fin ((chOne v0).c ⟨0, by omega⟩))) ((chOne v0).X ⟨0, by omega⟩) v x := by
  intro v x
  have h : (chainMat (chOne v0).Kj ⟨(ptQ 0 (fun _ => 1) 1 1).n + 1, by show 0 + 1 < 1 + 1; omega⟩).mulVec x = x :=
    (congrArg (fun M => Matrix.mulVec M x) chain_one).trans (Matrix.one_mulVec x)
  rw [h]
  rfl

theorem tieOne_isom (v0 : InfinitePlace K3) (v : InfinitePlace K3) (x : Fin ((chOne v0).c 0) → K3) :
    (ptQ 0 (fun _ => 1) 1 1).S₁.ipAt (ptQ 0 (fun _ => 1) 1 1).hS₁ v
        ((ptQ 0 (fun _ => 1) 1 1).col ((tieOne v0).coF 0 (Nat.zero_le _) x))
        ((ptQ 0 (fun _ => 1) 1 1).col ((tieOne v0).coF 0 (Nat.zero_le _) x)) =
      famIpAt ((ptQ 0 (fun _ => 1) 1 1).F 0) ((ptQ 0 (fun _ => 1) 1 1).hF 0) v ((tieOne v0).coF 0 (Nat.zero_le _) x)
        ((tieOne v0).coF 0 (Nat.zero_le _) x) := (tieOne v0).col_isom (chOne_isom v0) v x

theorem tieOne_first (v0 : InfinitePlace K3) : (tieOne v0).First ptInF := fun _ => rfl

end Formalism.L2.DIV.Inst
