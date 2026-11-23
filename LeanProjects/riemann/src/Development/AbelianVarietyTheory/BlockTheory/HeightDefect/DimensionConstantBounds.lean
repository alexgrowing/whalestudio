import Mathlib
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.Divisibility.WeightFamilies

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DimensionConstantBounds

open Formalism.BasicNotions Formalism.MainNotions.WeightFamilies NumberField

def Z {D : D7} (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L

def grade {D : D7} (L : SizeData₂ D) (CP : ℝ) (e : ℕ) : ℝ := CP * Z L ^ e

def PP {D : D7} (L : SizeData₂ D) (CP : ℝ) : ℝ := grade L CP 12

def lrd (D : D7) : ℝ := Real.log D.host.rdE

def RR (D : D7) : ℝ := D.host.rdE ^ 7

def q (D : D7) : ℕ := min (D.host.g 0) (D.host.g 1)

def r1 : ℕ := 5

def g0 (D : D7) : ℕ := 2 * r1 ^ 4 * D.R.r

def dimFlag (D : D7) : ℕ := D.R.f * D.R.r.choose 2

def dimX (D : D7) (j : ℕ) : ℕ := D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2

def degF {D : D7} {j : ℕ} (w : Wt D j) : ℕ := ∑ τ, ((∑ i, w.aP τ i) + ∑ i, w.aM τ i)

def cOf (D : D7) (P DF : ℝ) : ℝ := RR D * P * DF ^ 2 / (q D : ℝ)

def c {D : D7} (L : SizeData₂ D) (CP DF : ℝ) : ℝ := cOf D (PP L CP) DF

def LamStar (D : D7) : ℝ :=
  Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
    Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * (D.host.q : ℝ) * (D.host.d : ℝ))

def LamPlus (D : D7) (po : ℕ) : ℝ := LamStar D + 2 * Real.log (po : ℝ)

def IsOwnPrime (D : D7) (po : ℕ) : Prop := po = D.host.pde ∨ po = D.host.pde'

def PN {D : D7} (L : SizeData₂ D) : ℝ := 2 * L.sc.L + LamStar D + 4

def n0 (D : D7) (j : ℕ) : ℕ := D.R.r + 2 * g0 D * (dimX D j + 1)

def dimBoundMax (D : D7) : ℕ := D.R.r + 2 * g0 D * ((Finset.Icc 1 D.R.m).sup (dimX D) + 1)

def PUn (D : D7) (n : ℕ) : ℝ :=
  (D.R.f : ℝ) * (n : ℝ) * (2 * lrd D + 2 * Real.log ((D.R.f : ℝ) * (n : ℝ)) + 3)

def PU (D : D7) : ℝ := PUn D D.R.r

def PO {D : D7} (L : SizeData₂ D) : ℝ :=
  19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L + 198 * (D.R.f : ℝ) ^ 2 * L.sc.L

def sizeConstantAtWeight (D : D7) (nW : ℕ) : ℝ :=
  max (90 * ((D.R.f : ℝ) * (D.R.r : ℝ) + 1))
    (max (360 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3)
      (max (2 * (3 * (D.R.r : ℝ) + 3 + (D.R.r : ℝ) * Real.log (D.R.r : ℝ)))
        (max (nW : ℝ)
          (max (2 * (r1 : ℝ) ^ 4 * (D.R.r : ℝ))
            (max ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 6) 11)))))

def sizeConstantAtParamsWeight {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : ℝ := sizeConstantAtWeight D T.nWn

def DivisibilityWeightConstant (D : D7) : ℝ :=
  72 * (r1 : ℝ) ^ 4 * (dimFlag D : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 * (D.R.m : ℝ) ^ 4

def PI4 (D : D7) (PLam logNc : ℝ) : ℝ := 5 * (PLam + LamStar D) + 2 * logNc / (dimFlag D : ℝ)

def fieldSize (K : Type) [Field K] [NumberField K] : ℝ :=
  Real.log (Module.finrank ℚ K : ℝ) +
    Real.log (|((discr K : ℤ) : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ)))

def GOf {D : D7} (L : SizeData₂ D) (PLam : ℝ) (po : ℕ) (o : ℝ) : ℝ :=
  PLam + (3 * L.sc.L + 2 * o) + 2 * (D.R.f : ℝ) * (D.R.r : ℝ) * LamPlus D po + 31 * Z L

def G {D : D7} (L : SizeData₂ D) (X : Prov D) (PLam : ℝ) (po : ℕ) : ℝ :=
  GOf L PLam po (max (fieldSize X.KO) (fieldSize D.host.E))

def GWith {D : D7} (L : SizeData₂ D) (X : Prov D) (K' : Type) [Field K'] [NumberField K']
    (PLam : ℝ) (po : ℕ) : ℝ :=
  GOf L PLam po (max (fieldSize X.KO) (fieldSize K'))

def DomWith {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (Coo CP : ℝ) : Prop :=
  10 ^ 3 ≤ CP ∧ (Coo * CP) ^ 20 ≤ Z L ∧
  PU D ≤ grade L CP 1 ∧ LamStar D ≤ grade L CP 1 ∧ PN L ≤ grade L CP 1 ∧
  PO L ≤ grade L CP 2 ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (n0 D j : ℝ) ≤ grade L CP 3) ∧
  sizeConstantAtParamsWeight T ≤ grade L CP 4 ∧ DivisibilityWeightConstant D ≤ grade L CP 10

def Dom {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (CP : ℝ) : Prop :=
  DomWith T 1 CP

def DomArgs {D : D7} (L : SizeData₂ D) (X : Prov D) (CP PLam logNc : ℝ) (po : ℕ) : Prop :=
  LamPlus D po ≤ grade L CP 1 ∧ PLam ≤ grade L CP 1 ∧
  G L X PLam po ≤ grade L CP 2 ∧ PI4 D PLam logNc ≤ grade L CP 2

def RingBound {D : D7} (L : SizeData₂ D) (X : Prov D) : Prop :=
  Real.log (degO X) ≤ PO L ∧ Real.log (rdO X) ≤ PO L

def Sizes {D : D7} (L : SizeData₂ D) (C : ℝ) : Prop :=
  L.sc.x ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ∧
  logdE D / (2 * (D.R.f : ℝ)) + |L.logDerivativeAtOne| ≤ 2 * L.sc.L ∧
  L.sc.x ^ (-L.sc.eps) ≤ L.de2 ∧
  (∀ i, Real.log (D.host.g i : ℝ) ≤ 9 * L.sc.L + 1) ∧
  |L.logOm| ≤ C * L.sc.L ∧
  (Real.log (D.host.pde : ℝ) ≤ L.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ L.sc.L) ∧
  (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ D.host.rdE ^ 3

def Hyp {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (X : Prov D) (CP C : ℝ) : Prop :=
  Dom T CP ∧ RingBound L X ∧ Sizes L C

theorem Z_eq {D : D7} (L : SizeData₂ D) : Z L = zBase L := rfl

theorem PP_eq_PPv {D : D7} (L : SizeData₂ D) (CP : ℝ) : PP L CP = PPv D L CP 12 := by
  unfold PP grade PPv
  rw [Z_eq, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem PP_eq_of_eP_eq_twelve {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (h : T.eP = 12) :
    PP L T.CP = T.PP := by
  rw [PP_eq_PPv, ← h, PPv_rec]

theorem RR_eq (D : D7) : RR D = RRv D 7 := by
  unfold RR RRv
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem f_pos (D : D7) : 0 < D.R.f := by
  unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega

theorem lrd_eq (D : D7) : lrd D = logdE D / (2 * (D.R.f : ℝ)) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast f_pos D
  rw [logdE_eq_rd]; unfold lrd; field_simp

theorem q_pos (D : D7) : 0 < q D :=
  lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem dimFlag_pos (D : D7) : 0 < dimFlag D := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hr : 2 ≤ D.R.r := by unfold Ranks.r; omega
  exact Nat.mul_pos (f_pos D) (Nat.choose_pos hr)

theorem Dp_eq {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : T.Dp = dimFlag D := T.Dp_eq

theorem half_f (D : D7) : (D.R.f : ℝ) / 2 = D.R.n := by
  unfold Ranks.f; push_cast; ring

theorem fieldSize_O {D : D7} (X : Prov D) :
    fieldSize X.KO = Real.log (degO X) + Real.log (rdO X) := rfl

theorem fieldSize_E (D : D7) :
    fieldSize D.host.E = Real.log (Module.finrank ℚ D.host.E : ℝ) + lrd D := rfl

theorem logdE_nonneg (D : D7) : 0 ≤ logdE D := by
  unfold logdE
  apply Real.log_nonneg
  have h : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast h

theorem Sizes.halves {D : D7} {L : SizeData₂ D} {C : ℝ} (h : Sizes L C) :
    logdE D ≤ 4 * (D.R.f : ℝ) * L.sc.L ∧ |L.logDerivativeAtOne| ≤ 2 * L.sc.L := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast f_pos D
  have h1 := h.2.1
  have h2 : 0 ≤ logdE D / (2 * (D.R.f : ℝ)) := div_nonneg (logdE_nonneg D) (by positivity)
  have h3 := abs_nonneg L.logDerivativeAtOne
  refine ⟨?_, by linarith⟩
  have h4 : logdE D / (2 * (D.R.f : ℝ)) ≤ 2 * L.sc.L := by linarith
  rw [div_le_iff₀ (by positivity)] at h4
  linarith

theorem dimBound_le_dimBoundMax (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : n0 D j ≤ dimBoundMax D := by
  unfold n0 dimBoundMax
  have : dimX D j ≤ (Finset.Icc 1 D.R.m).sup (dimX D) := Finset.le_sup (Finset.mem_Icc.2 ⟨h1, h2⟩)
  gcongr

end GlobalTheory.IndefiniteRowSideFullHecke.DimensionConstantBounds

end
