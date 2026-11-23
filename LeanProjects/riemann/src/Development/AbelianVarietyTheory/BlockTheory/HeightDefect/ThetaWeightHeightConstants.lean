import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParamsT

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

open Formalism.BasicNotions NumberField

def Lift (R : Ranks) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

def pSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).1

def qSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).2

theorem pSig_pos {R : Ranks} (j : Lift R) : 0 < pSig j := by
  have := R.m_add_three_le_k; have := j.2.1
  simp only [pSig, Ranks.sigW]; omega

theorem pSig_add_qSig {R : Ranks} (j : Lift R) : pSig j + qSig j = R.r := by
  have := R.m_add_three_le_k; have := j.2.1; have := j.2.2
  simp only [pSig, qSig, Ranks.sigW, Ranks.r]; omega

def IsTotIsotropic {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (U : Submodule E S.V) : Prop := ∀ x ∈ U, ∀ y ∈ U, S.hD x y = 0

def isotropicDims {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Set ℕ :=
  {n | ∃ U : Submodule E S.V, IsTotIsotropic S U ∧ Module.finrank E U = n}

def wittIndexOf {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : ℕ :=
  sSup (isotropicDims S)

theorem wittIndexOf_isGreatest {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    IsGreatest (isotropicDims S) (wittIndexOf S) := by
  have hb : BddAbove (isotropicDims S) := by
    refine ⟨Module.finrank E S.V, ?_⟩
    rintro n ⟨U, -, rfl⟩
    exact Submodule.finrank_le U
  have hn : (isotropicDims S).Nonempty := by
    refine ⟨_, ⊥, ?_, rfl⟩
    intro x _ y hy
    rw [(Submodule.mem_bot E).1 hy]
    simp [HSpace.hD]
  exact ⟨Nat.sSup_mem hn hb, fun n h => le_csSup hb h⟩

def wittIndex (D : D7) (j : Lift D.R) : ℕ :=
  letI := D.host.cmStar; wittIndexOf (D.sp.W j.1)

def rho {R : Ranks} (j : Lift R) : ℕ := R.m - j.1

theorem rho_eq_qSig {R : Ranks} (j : Lift R) : rho j = qSig j := rfl

def WittIndexEq : Prop := ∀ (D : D7) (j : Lift D.R), wittIndex D j = rho j

def dPrime {R : Ranks} (j : Lift R) : ℕ := 2 * R.f * rho j

theorem dPrime_le {R : Ranks} (j : Lift R) : dPrime j ≤ 2 * R.f * R.m :=
  Nat.mul_le_mul_left _ (Nat.sub_le _ _)

def dimBase {R : Ranks} (j : Lift R) : ℕ := R.f * pSig j * qSig j

def dimFlag {R : Ranks} (j : Lift R) : ℕ :=
  dimBase j + R.f * (pSig j * (pSig j - 1) / 2 + qSig j * (qSig j - 1) / 2)

def DimFlagEq : Prop := ∀ (R : Ranks) (j : Lift R), dimFlag j = R.f * R.r.choose 2

def RR (D : D7) : ℝ := D.host.rdE ^ 7

def PP {D : D7} (L : SizeData₂ D) (C e : ℝ) : ℝ := C * ((D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L) ^ e

theorem PP_eq_params {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    PP L T.CP T.eP = T.PP := T.PP_eq.symm

def lrd (D : D7) : ℝ := Real.log D.host.rdE

def lc (D : D7) : ℝ := Real.log (Ideal.absNorm D.host.ccK : ℝ)

def logG (D : D7) : ℝ := Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)

def PU (D : D7) (n : ℕ) : ℝ :=
  (D.R.f : ℝ) * n * (2 * lrd D + 2 * Real.log ((D.R.f : ℝ) * n) + 3)

def primePairSetFirst (D : D7) : ℝ := 2 * PU D D.R.r + Real.log (2 * (D.R.m : ℝ)) + lc D

def PPcnt (D : D7) : ℝ := logG D + 2 * lrd D + primePairSetFirst D + 1

def FirstNormConstantMax (D : D7) : ℝ := 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2

def Pdeg {D : D7} (L : SizeData₂ D) : ℝ := (1 + |L.logOm|) / 2

def heightConstantExplicitFormula {D : D7} (L : SizeData₂ D) : ℝ :=
  3 * lrd D + 4 * Real.pi * (FirstNormConstantMax D * (PPcnt D + Real.log (4 * FirstNormConstantMax D)) + 4) + primePairSetFirst D +
    2 * Real.log (2 * (D.R.f : ℝ) * (D.R.r : ℝ)) + 1 + Pdeg L

def heightConstantMaxForm {D : D7} (L : SizeData₂ D) (C₄ : ℝ) : ℝ := max (heightConstantExplicitFormula L) (Pdeg L + C₄ * zBase L)

def heightConstantAffineSum {D : D7} (L : SizeData₂ D) (C₄ : ℝ) : ℝ := heightConstantExplicitFormula L + (Pdeg L + C₄ * zBase L)

def PolynomialFractionProfile (D : D7) (x : ℝ) : ℝ := 3 * x + 3 * lrd D + 3

def degreeThreePolynomialMajorant {D : D7} (L : SizeData₂ D) (C : ℝ) (e : ℕ) : ℝ :=
  C * ((D.R.f : ℝ) * (D.R.r : ℝ) + Real.log L.sc.b + logdE D + |L.logOm|) ^ e

theorem log_b {D : D7} (L : SizeData₂ D) : Real.log L.sc.b = L.sc.L := Real.log_exp _

def SizeRows {D : D7} (L : SizeData₂ D) : Prop :=
  D.R.m ^ 2 ≤ D.R.r ∧ (∀ i, Real.log (D.host.g i : ℝ) ≤ 9 * L.sc.L + 1) ∧ lc D ≤ L.sc.L

def HeightConstantLePolynomial : Prop := ∀ C₄ : ℝ, 0 ≤ C₄ → ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (L : SizeData₂ D), SizeRows L →
  heightConstantMaxForm L C₄ ≤ heightConstantAffineSum L C₄ ∧ heightConstantAffineSum L C₄ ≤ degreeThreePolynomialMajorant L C 3

def HeightConstantDegreeThree : Prop := ∀ C₄ c : ℝ, 0 ≤ C₄ → ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (L : SizeData₂ D),
  SizeRows L → lrd D ≤ L.sc.L → Real.log (D.R.f : ℝ) ≤ L.sc.L → Real.log (D.R.r : ℝ) ≤ L.sc.L →
  |L.logOm| ≤ c * zBase L → heightConstantAffineSum L C₄ ≤ PP L C 3

@[ext] structure ThetaWeight (D : D7) (j : Lift D.R) where
  plus : D.what₂.Tau → Fin (pSig j) → ℤ
  minus : D.what₂.Tau → Fin (qSig j) → ℤ
  plus_anti : ∀ τ, Antitone (plus τ)
  minus_anti : ∀ τ, Antitone (minus τ)
  n : ℕ

namespace ThetaWeight

variable {D : D7} {j : Lift D.R}

def add (G G' : ThetaWeight D j) : ThetaWeight D j where
  plus := G.plus + G'.plus
  minus := G.minus + G'.minus
  plus_anti τ := (G.plus_anti τ).add (G'.plus_anti τ)
  minus_anti τ := (G.minus_anti τ).add (G'.minus_anti τ)
  n := G.n + G'.n

def nsmul (N : ℕ) (G : ThetaWeight D j) : ThetaWeight D j where
  plus τ i := N * G.plus τ i
  minus τ i := N * G.minus τ i
  plus_anti τ _ _ h := mul_le_mul_of_nonneg_left (G.plus_anti τ h) (by positivity)
  minus_anti τ _ _ h := mul_le_mul_of_nonneg_left (G.minus_anti τ h) (by positivity)
  n := N * G.n

def DF (G : ThetaWeight D j) : ℤ := ∑ τ, ((∑ i, G.plus τ i) + ∑ i, G.minus τ i)

def size (G : ThetaWeight D j) : ℤ :=
  G.DF + ((D.R.f * max (rho j) 1 * D.R.r * G.n : ℕ) : ℤ) + 1

def plusLast (G : ThetaWeight D j) (τ : D.what₂.Tau) : ℤ :=
  G.plus τ ⟨pSig j - 1, Nat.sub_lt (pSig_pos j) one_pos⟩

def Dominant (G : ThetaWeight D j) : Prop := ∀ τ, (∀ i, 0 ≤ G.plus τ i) ∧ ∀ i, 0 ≤ G.minus τ i

def PlusLastPos (G : ThetaWeight D j) : Prop := ∀ τ, 1 ≤ G.plusLast τ

def PlusLastPosAtOne (G : ThetaWeight D j) : Prop := ∃ τ, 1 ≤ G.plusLast τ

theorem size_add (G G' : ThetaWeight D j) : (G.add G').size = G.size + G'.size - 1 := by
  simp only [size, DF, add, Pi.add_apply, Finset.sum_add_distrib]
  push_cast; ring

theorem size_nsmul_le (N : ℕ) (hN : 1 ≤ N) (G : ThetaWeight D j) :
    (G.nsmul N).size ≤ N * G.size := by
  have h : (G.nsmul N).DF = N * G.DF := by
    simp only [DF, nsmul, Finset.mul_sum, mul_add]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hn : (G.nsmul N).n = N * G.n := rfl
  unfold size
  rw [h, hn]; push_cast; nlinarith

theorem one_le_size {G : ThetaWeight D j} (h : G.Dominant) : 1 ≤ G.size := by
  have : 0 ≤ G.DF := Finset.sum_nonneg fun τ _ =>
    add_nonneg (Finset.sum_nonneg fun i _ => (h τ).1 i) (Finset.sum_nonneg fun i _ => (h τ).2 i)
  unfold size; omega

end ThetaWeight

def EvenThetaWeight (D : D7) (j : Lift D.R) : Type := {G : ThetaWeight D j // Even G.n}

def DomEvenThetaWeight (D : D7) (j : Lift D.R) : Type :=
  {G : ThetaWeight D j // G.Dominant ∧ Even G.n}

def SizeLower : Prop := ∀ (D : D7) (j : Lift D.R) (G : ThetaWeight D j),
  G.DF + ((D.R.f * D.R.r * G.n : ℕ) : ℤ) ≤ G.size ∧ G.DF + ((D.R.f * rho j * G.n : ℕ) : ℤ) ≤ G.size

def staircase (D : D7) (j : Lift D.R) : ThetaWeight D j where
  plus _ i := (pSig j : ℤ) - i.1
  minus _ i := (qSig j : ℤ) - i.1
  plus_anti _ a b h := by have : a.1 ≤ b.1 := h; simp only; omega
  minus_anti _ a b h := by have : a.1 ≤ b.1 := h; simp only; omega
  n := 2

example (D : D7) (j : Lift D.R) :
    (staircase D j).Dominant ∧ (staircase D j).PlusLastPos ∧ Even (staircase D j).n := by
  refine ⟨fun τ => ⟨fun i => ?_, fun i => ?_⟩, fun τ => ?_, by simp [staircase]⟩
  · have := i.2; simp only [staircase]; omega
  · have := i.2; simp only [staircase]; omega
  · have := pSig_pos j; simp only [ThetaWeight.plusLast, staircase]; omega

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

end
