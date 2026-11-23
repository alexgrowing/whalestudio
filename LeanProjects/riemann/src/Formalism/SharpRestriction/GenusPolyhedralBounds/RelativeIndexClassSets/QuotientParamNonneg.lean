import Formalism.FilteredPoleLength.LocalDescentLevels.FourTermSumBoundOfParameters

noncomputable section

namespace Formalism.MainNotions.Gaps.T0

theorem levels_real (A B R δ d D T cg c w G PH Pη L F' fr aδ aF HF Hδ SS Λ' lδ : ℝ)
    (hR : 0 ≤ R) (hRδ : R * δ ≤ d) (hδ : 0 ≤ δ) (hlδ : 0 ≤ lδ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hcg0 : 0 ≤ cg) (hcg1 : cg ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ PH * L) (hG : 0 ≤ G) (hPH : 0 ≤ PH)
    (hPη : 0 ≤ Pη) (hL : 0 ≤ L) (hfr : 0 ≤ fr)
    (h1 : 2 * A ≤ δ * lδ + 2 * SS + 2 * D * aF * w + 2 * HF)
    (h2 : B ≤ cg * (Hδ + D * aδ * w) + T * c * δ * Pη)
    (hSS : SS ≤ δ * Λ') (hΛ : Λ' ≤ G * F') (hF : F' ≤ (D + 2) * L + 5 * fr * T)
    (haδ : aδ ≤ 4 / 3 * δ) (haF : aF ≤ 4 / 3 * (D + 4) * δ)
    (hHF : HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    (hHδ : Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L) :
    R * (A + 1 / 2 * B) ≤
      d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
  have hSS' : SS ≤ δ * (G * ((D + 2) * L + 5 * fr * T)) :=
    hSS.trans (mul_le_mul_of_nonneg_left (hΛ.trans (mul_le_mul_of_nonneg_left hF hG)) hδ)
  have haFw : aF * w ≤ 4 / 3 * (D + 4) * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haF hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haFw' : D * (aF * w) ≤ D * (4 / 3 * (D + 4) * δ * (PH * L)) := mul_le_mul_of_nonneg_left haFw hD
  have haδw : aδ * w ≤ 4 / 3 * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haδ hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haδw' : D * (aδ * w) ≤ D * (4 / 3 * δ * (PH * L)) := mul_le_mul_of_nonneg_left haδw hD
  have hXb0 : 0 ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by positivity
  have hin : Hδ + D * aδ * w ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by
    have e : D * aδ * w = D * (aδ * w) := by ring
    linarith
  have hB' : B ≤ ((D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L))) + T * c * δ * Pη := by
    have e2 := mul_le_mul_of_nonneg_left hin hcg0
    have e3 := mul_le_of_le_one_left hXb0 hcg1
    linarith
  have hAB : A + 1 / 2 * B ≤ δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
    have p1 : 0 ≤ δ * G * L * D ^ 2 := by positivity
    have p2 : 0 ≤ δ * G * L * D := by positivity
    have p3 : 0 ≤ δ * G * L := by positivity
    have p4 : 0 ≤ δ * PH * L * D ^ 2 := by positivity
    have p5 : 0 ≤ δ * PH * L * D := by positivity
    have p6 : 0 ≤ δ * PH * L := by positivity
    have p7 : 0 ≤ δ * lδ := by positivity
    have e : D * aF * w = D * (aF * w) := by ring
    linarith
  have hT0 : 0 ≤ ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by positivity
  calc R * (A + 1 / 2 * B) ≤ R * (δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)) := mul_le_mul_of_nonneg_left hAB hR
    _ = (R * δ) * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by ring
    _ ≤ d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := mul_le_mul_of_nonneg_right hRδ hT0

theorem total_named_real (d D T c G PH Pη Pd PD PQ DivisibilityWeightConstant RR γ L κ fr lδ ρ ρ' : ℝ)
    (hd : 0 ≤ d) (hD : 1 ≤ D) (hT : 1 ≤ T) (hG : 0 ≤ G) (hPH : 0 ≤ PH) (hPD : 0 ≤ PD) (hPQ : 0 ≤ PQ)
    (hκ : 0 ≤ κ) (hS2 : T * L ≤ 2 * κ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd)
    (hρ : ρ ≤ ρ' + 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ)) :
    d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)
        + ρ * PD * κ + ρ' * PQ * κ ≤
      d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) := by
  have hT0 : 0 < T := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hLT : L ≤ 2 * κ / T := by
    rw [le_div_iff₀ hT0]
    linarith
  have hDD : (D + 4) * (D + 1) ≤ 10 * D ^ 2 := by nlinarith
  have hk : 0 ≤ 2 * κ / T := by positivity
  have hGP : 0 ≤ 3 * G + 9 * PH := by positivity
  have e1 : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L ≤ (60 * G + 180 * PH) * D ^ 2 * κ / T := by
    calc (D + 4) * (D + 1) * (3 * G + 9 * PH) * L
        ≤ (D + 4) * (D + 1) * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_left hLT (by positivity)
      _ ≤ 10 * D ^ 2 * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hGP) hk
      _ = (60 * G + 180 * PH) * D ^ 2 * κ / T := by ring
  have hPd0 : 0 ≤ Pd := le_trans hlδ0 hlδ
  have e2 : lδ ≤ Pd * T := hlδ.trans (le_mul_of_one_le_right hPd0 hT)
  have hX : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη ≤ ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) := by
    have ea : (5 * G * fr + Pd) * T = 5 * G * fr * T + Pd * T := by ring
    have eb : Pη / 2 * T * c = 1 / 2 * T * c * Pη := by ring
    linarith
  have g1 := mul_le_mul_of_nonneg_left hX hd
  have f1 : ρ * (PD * κ) ≤ (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) :=
    mul_le_mul_of_nonneg_right hρ (mul_nonneg hPD hκ)
  have f2 : ρ' * ((PD + PQ) * κ) ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) :=
    mul_le_mul_of_nonneg_right hρ' (mul_nonneg (add_nonneg hPD hPQ) hκ)
  have e5 : 22 * D ^ 2 * d / T * (PD * κ) ≤ d * (40 * PD * D ^ 2 * κ / T) := by
    have h0 : 0 ≤ d * PD * D ^ 2 * κ / T := by positivity
    have ea : 22 * D ^ 2 * d / T * (PD * κ) = 22 * (d * PD * D ^ 2 * κ / T) := by ring
    have eb : d * (40 * PD * D ^ 2 * κ / T) = 40 * (d * PD * D ^ 2 * κ / T) := by ring
    rw [ea, eb]
    linarith
  have eq1 : d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) =
      d * ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) + d * (40 * PD * D ^ 2 * κ / T) +
        d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) := by ring
  have eq2 : ρ * PD * κ + ρ' * PQ * κ = ρ * (PD * κ) + ρ' * ((PD + PQ) * κ) - ρ' * (PD * κ) := by ring
  have eq3 : (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) = ρ' * (PD * κ) + 22 * D ^ 2 * d / T * (PD * κ) := by
    ring
  rw [eq1]
  linarith

theorem total_le_of_bounds (d D T c RR γ κ P1 P2 P3 P4 PP : ℝ)
    (hd : 0 ≤ d) (hT : 0 < T) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (h1 : P1 * D ^ 2 ≤ PP ^ 2 * D ^ 3) (h2 : P2 ≤ PP ^ 3) (h3 : P3 ≤ PP ^ 2) (h4 : P4 ≤ PP ^ 2) :
    d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ) ≤
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by
  have a1 : P1 * D ^ 2 * (κ / T) ≤ PP ^ 2 * D ^ 3 * (κ / T) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have a2 : P2 * T ≤ PP ^ 3 * T := mul_le_mul_of_nonneg_right h2 hT.le
  have a3 : P3 * (T * c) ≤ PP ^ 2 * (T * c) := mul_le_mul_of_nonneg_right h3 (by positivity)
  have a4 : P4 * ((1 / T + RR ^ 2 * c) * κ / γ) ≤ PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hsum : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ ≤
      PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T := by
    have e : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ =
        P1 * D ^ 2 * (κ / T) + P2 * T + P3 * (T * c) + P4 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    have e' : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T =
        PP ^ 2 * D ^ 3 * (κ / T) + PP ^ 3 * T + PP ^ 2 * (T * c) + PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    rw [e, e']
    linarith
  calc d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ)
      ≤ d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T) :=
        mul_le_mul_of_nonneg_left hsum hd
    _ = d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by ring

structure SumDat (ι : Type*) where

  s : Finset ι

  l : ι → ℝ

  I : ι → ℝ

  N : ι → ℝ

  cD : ι → ℝ

  vQ : ι → ℝ

  be : ι → ℝ

  (R δ d D T c i g₀ rw : ℝ)

  (G PH Prw Pη Pd PD PQ DivisibilityWeightConstant RR γ₀ : ℝ)

  (L κ F' f r : ℝ)

  (aδ aF HF Hδ SS Λ' : ℝ)

  (ρ ρ' : ℝ)

namespace SumDat

variable {ι : Type*} (X : SumDat ι)

def rr (la : ι) : ℝ :=
  X.R * (X.I la + X.T * (X.c / (2 * X.i)) * X.N la) + X.cD la + (X.vQ la + X.ρ' * X.be la)

def P1 : ℝ := 60 * X.G + 180 * X.PH + 40 * X.PD

def P2 : ℝ := 5 * X.G * (X.f * X.r ^ 2) + X.Pd

def P3 : ℝ := X.Pη / 2

def P4 : ℝ := X.DivisibilityWeightConstant * (X.PD + X.PQ)

def lev : ℝ :=
  (X.D + 4) * (X.D + 1) * (3 * X.G + 9 * X.PH) * X.L + 5 * X.G * (X.f * X.r ^ 2) * X.T + Real.log X.δ
    + 1 / 2 * X.T * X.c * X.Pη

def totalNamed : ℝ :=
  X.d * (X.P1 * X.D ^ 2 * X.κ / X.T + X.P2 * X.T + X.P3 * X.T * X.c
    + X.P4 * (1 / X.T + X.RR ^ 2 * X.c) * X.κ / X.γ₀)

def total (PP : ℝ) : ℝ :=
  X.d * PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀)
    + X.d * PP ^ 3 * X.T

structure Ok : Prop where

  R0 : 0 ≤ X.R
  δ1 : 1 ≤ X.δ
  D1 : 1 ≤ X.D
  T1 : 1 ≤ X.T
  c0 : 0 ≤ X.c
  g0 : 0 ≤ X.g₀
  rw1 : 1 ≤ X.rw
  G0 : 0 ≤ X.G
  height_param_nonneg : 0 ≤ X.PH
  Pη0 : 0 ≤ X.Pη
  BaseRankDimension : 0 ≤ X.PD
  quotient_param_nonneg : 0 ≤ X.PQ
  f0 : 0 ≤ X.f
  L0 : 0 ≤ X.L
  κ0 : 0 ≤ X.κ
  γ0 : 0 < X.γ₀

  Rδ : X.R * X.δ ≤ X.d

  Tcg : X.T * X.c * X.g₀ ≤ 1

  PrwPH : X.Prw ≤ X.PH

  lrw : Real.log X.rw + 1 / 2 ≤ X.Prw * X.L

  lev1 : 2 * ∑ la ∈ X.s, X.I la * X.l la ≤
    X.δ * Real.log X.δ + 2 * X.SS + 2 * X.D * X.aF * (Real.log X.rw + 1 / 2) + 2 * X.HF

  lev2 : X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la ≤
    X.T * X.c * X.g₀ * (X.Hδ + X.D * X.aδ * (Real.log X.rw + 1 / 2)) + X.T * X.c * X.δ * X.Pη

  SSle : X.SS ≤ X.δ * X.Λ'

  S4 : X.Λ' ≤ X.G * X.F'

  S3 : X.F' ≤ (X.D + 2) * X.L + 5 * (X.f * X.r ^ 2) * X.T

  S2 : X.T * X.L ≤ 2 * X.κ

  lδ : Real.log X.δ ≤ X.Pd

  aδle : X.aδ ≤ 4 / 3 * X.δ

  aFle : X.aF ≤ 4 / 3 * (X.D + 4) * X.δ

  HFle : X.HF ≤ (X.D + 4) * (X.D + 1) * X.δ * (2 * X.G + 6 * X.PH) * X.L

  Hδle : X.Hδ ≤ (X.D + 1) * X.δ * (2 * X.G + 6 * X.PH) * X.L

  deep : ∑ la ∈ X.s, X.cD la * X.l la ≤ X.ρ * X.PD * X.κ

  quot : ∑ la ∈ X.s, (X.vQ la + X.ρ' * X.be la) * X.l la ≤ X.ρ' * X.PQ * X.κ

  shρ : X.ρ ≤ X.ρ' + 22 * X.D ^ 2 * X.d / X.T

  shρ' : X.ρ' ≤ X.d * (X.DivisibilityWeightConstant * (X.RR ^ 2 * X.c + 1 / X.T) / X.γ₀)

structure Rel (PP : ℝ) : Prop where
  r1 : X.P1 * X.D ^ 2 ≤ PP ^ 2 * X.D ^ 3
  r2 : X.P2 ≤ PP ^ 3
  r3 : X.P3 ≤ PP ^ 2
  r4 : X.P4 ≤ PP ^ 2

structure Page (PP C k b m δ₂ q DF : ℝ) : Prop where
  tableDegreeThreeBase : 0 < PP
  one_le_radius_alt : 1 ≤ X.RR
  q0 : 0 < q
  C0 : 0 ≤ C
  k0 : 0 ≤ k
  b0 : 0 ≤ b
  m0 : 0 < m
  δ₂0 : 0 < δ₂

  Tγ : X.T ≤ X.γ₀

  S1 : X.κ ≤ C * k * X.f * b

  ps0 : PP ^ 3 * X.T ≤ X.f * m * b * δ₂ / 4

  ps1 : 4 * C * PP ^ 2 * X.D ^ 3 * k / (m * δ₂) ≤ X.T

  cdef : X.c = X.RR * PP * DF ^ 2 / q
  g1 : 1 ≤ X.g₀

  qlow : X.RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q

  TPP : PP ^ 2 ≤ X.T

  primeSetTwoBounds : 2 ≤ PP ^ 2

variable {X}

theorem Ok.d0 (h : X.Ok) : 0 ≤ X.d := le_trans (mul_nonneg h.R0 (by linarith [h.δ1])) h.Rδ

theorem sum_split (X : SumDat ι) :
    ∑ la ∈ X.s, X.rr la * X.l la =
      X.R * (∑ la ∈ X.s, X.I la * X.l la + 1 / 2 * (X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la))
        + ∑ la ∈ X.s, X.cD la * X.l la + ∑ la ∈ X.s, (X.vQ la + X.ρ' * X.be la) * X.l la := by
  have e : ∀ la, X.rr la * X.l la = X.R * (X.I la * X.l la) +
      X.R * (1 / 2 * (X.T * (X.c / X.i))) * (X.N la * X.l la) + X.cD la * X.l la +
        (X.vQ la + X.ρ' * X.be la) * X.l la := fun la => by
    unfold SumDat.rr
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem Ok.levels (h : X.Ok) :
    X.R * (∑ la ∈ X.s, X.I la * X.l la + 1 / 2 * (X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la)) ≤
      X.d * X.lev := by
  have hδ0 : 0 ≤ X.δ := by linarith [h.δ1]
  have hw0 : 0 ≤ Real.log X.rw + 1 / 2 := by linarith [Real.log_nonneg h.rw1]
  have hw : Real.log X.rw + 1 / 2 ≤ X.PH * X.L := h.lrw.trans (mul_le_mul_of_nonneg_right h.PrwPH h.L0)
  have hcg0 : 0 ≤ X.T * X.c * X.g₀ := mul_nonneg (mul_nonneg (by linarith [h.T1]) h.c0) h.g0
  have key := levels_real _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.R0 h.Rδ hδ0
    (Real.log_nonneg h.δ1) (by linarith [h.D1]) (by linarith [h.T1]) h.c0 hcg0 h.Tcg hw0 hw h.G0 h.height_param_nonneg
    h.Pη0 h.L0 (mul_nonneg h.f0 (sq_nonneg X.r)) h.lev1 h.lev2 h.SSle h.S4 h.S3 h.aδle h.aFle h.HFle h.Hδle
  unfold SumDat.lev
  exact key

theorem Ok.sum_le_named (h : X.Ok) : ∑ la ∈ X.s, X.rr la * X.l la ≤ X.totalNamed := by
  rw [sum_split]
  have hL := h.levels
  have key := total_named_real (fr := X.f * X.r ^ 2) (Pη := X.Pη) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h.d0 h.D1 h.T1 h.G0 h.height_param_nonneg h.BaseRankDimension h.quotient_param_nonneg h.κ0 h.S2 (Real.log_nonneg h.δ1) h.lδ h.shρ h.shρ'
  unfold SumDat.totalNamed SumDat.P1 SumDat.P2 SumDat.P3 SumDat.P4
  unfold SumDat.lev at hL
  linarith [h.deep, h.quot]

theorem Ok.named_le_total (h : X.Ok) {PP : ℝ} (hP : X.Rel PP) : X.totalNamed ≤ X.total PP := by
  unfold SumDat.totalNamed SumDat.total
  exact total_le_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ h.d0 (by linarith [h.T1]) h.c0 h.κ0 h.γ0 hP.r1 hP.r2 hP.r3 hP.r4

theorem Ok.sum_le_total (h : X.Ok) {PP : ℝ} (hP : X.Rel PP) :
    ∑ la ∈ X.s, X.rr la * X.l la ≤ X.total PP := (h.sum_le_named).trans (h.named_le_total hP)

theorem Ok.total_le_page (h : X.Ok) {PP C k b m δ₂ q DF : ℝ} (hp : X.Page PP C k b m δ₂ q DF) :
    X.total PP ≤ X.d * X.f * m * b * δ₂ := by
  obtain ⟨tableDegreeThreeBase, one_le_radius_alt, q0, C0, k0, b0, m0, δ₂0, Tγ, S1, ps0, ps1, cdef, g1, qlow, TPP, primeSetTwoBounds⟩ := hp
  have T0 : 0 < X.T := by linarith [h.T1]
  have hD3 : 1 ≤ X.D ^ 3 := one_le_pow₀ h.D1
  have f0 := h.f0
  have κ0 := h.κ0
  have γ0 := h.γ0
  have d0 := h.d0
  have hc0 := h.c0
  have mδ : 0 < m * δ₂ := mul_pos m0 δ₂0
  have ps1' : 4 * C * PP ^ 2 * X.D ^ 3 * k ≤ X.T * (m * δ₂) := by
    rw [div_le_iff₀ mδ] at ps1
    linarith
  have primePairSetFirst : 1 ≤ PP := by nlinarith
  have cubicPeriodConstant : 1 ≤ PP ^ 3 := one_le_pow₀ primePairSetFirst
  have hq : X.RR * PP ^ 3 * DF ^ 2 ≤ q := by
    have hR4 : X.RR ≤ X.RR ^ 4 := le_self_pow₀ one_le_radius_alt (by norm_num)
    calc X.RR * PP ^ 3 * DF ^ 2 = X.RR * (PP ^ 3 * DF ^ 2) := by ring
      _ ≤ X.RR ^ 4 * (PP ^ 3 * DF ^ 2) := mul_le_mul_of_nonneg_right hR4 (by positivity)
      _ = X.RR ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := qlow
  have hq3 : X.RR ^ 3 * PP ^ 3 * DF ^ 2 ≤ q := by
    have hR4 : X.RR ^ 3 ≤ X.RR ^ 4 := pow_le_pow_right₀ one_le_radius_alt (by norm_num)
    calc X.RR ^ 3 * PP ^ 3 * DF ^ 2 = X.RR ^ 3 * (PP ^ 3 * DF ^ 2) := by ring
      _ ≤ X.RR ^ 4 * (PP ^ 3 * DF ^ 2) := mul_le_mul_of_nonneg_right hR4 (by positivity)
      _ = X.RR ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := qlow
  have hc1 : PP ^ 2 * X.c ≤ 1 := by
    rw [cdef, show PP ^ 2 * (X.RR * PP * DF ^ 2 / q) = X.RR * PP ^ 3 * DF ^ 2 / q by ring,
      div_le_one q0]
    exact hq
  have hc2 : PP ^ 2 * (X.RR ^ 2 * X.c) ≤ 1 := by
    rw [cdef, show PP ^ 2 * (X.RR ^ 2 * (X.RR * PP * DF ^ 2 / q)) = X.RR ^ 3 * PP ^ 3 * DF ^ 2 / q by ring,
      div_le_one q0]
    exact hq3
  have hT1 : PP ^ 2 / X.T ≤ 1 := (div_le_one T0).mpr TPP
  have tA : PP ^ 2 * X.D ^ 3 * X.κ / X.T ≤ X.f * m * b * δ₂ / 4 := by
    rw [div_le_iff₀ T0]
    have e1 : PP ^ 2 * X.D ^ 3 * X.κ ≤ PP ^ 2 * X.D ^ 3 * (C * k * X.f * b) :=
      mul_le_mul_of_nonneg_left S1 (by positivity)
    have e2 : (4 * C * PP ^ 2 * X.D ^ 3 * k) * (X.f * b) ≤ (X.T * (m * δ₂)) * (X.f * b) :=
      mul_le_mul_of_nonneg_right ps1' (by positivity)
    linarith
  have tB : PP ^ 2 * (X.T * X.c) ≤ X.f * m * b * δ₂ / 4 := by
    have e : PP ^ 2 * (X.T * X.c) = X.T * (PP ^ 2 * X.c) := by ring
    have e2 : X.T * (PP ^ 2 * X.c) ≤ X.T := mul_le_of_le_one_right T0.le hc1
    have e3 : X.T ≤ PP ^ 3 * X.T := le_mul_of_one_le_left T0.le cubicPeriodConstant
    linarith
  have tC : PP ^ 2 * ((X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) ≤ X.f * m * b * δ₂ / 4 := by
    have e1 : PP ^ 2 * (X.RR ^ 2 * X.c + 1 / X.T) ≤ 2 := by
      have e : PP ^ 2 * (X.RR ^ 2 * X.c + 1 / X.T) = PP ^ 2 * (X.RR ^ 2 * X.c) + PP ^ 2 / X.T := by ring
      linarith
    have e2 : X.κ / X.γ₀ ≤ X.κ / X.T := div_le_div_of_nonneg_left κ0 T0 Tγ
    have e3 : X.κ / X.T ≤ X.f * m * b * δ₂ / 8 := by
      rw [div_le_iff₀ T0]
      have hCk : 0 ≤ C * k := mul_nonneg C0 k0
      have a0 : 2 ≤ PP ^ 2 * X.D ^ 3 := by nlinarith
      have a1 : C * k * 2 ≤ C * k * (PP ^ 2 * X.D ^ 3) := mul_le_mul_of_nonneg_left a0 hCk
      have a2 : 8 * (C * k) * (X.f * b) ≤ X.T * (m * δ₂) * (X.f * b) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    calc PP ^ 2 * ((X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀)
        = (PP ^ 2 * (X.RR ^ 2 * X.c + 1 / X.T)) * (X.κ / X.γ₀) := by ring
      _ ≤ 2 * (X.κ / X.T) := mul_le_mul e1 e2 (by positivity) (by norm_num)
      _ ≤ X.f * m * b * δ₂ / 4 := by linarith
  have hsum : PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) +
      PP ^ 3 * X.T ≤ X.f * m * b * δ₂ := by
    have e : PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) =
        PP ^ 2 * X.D ^ 3 * X.κ / X.T + PP ^ 2 * (X.T * X.c) +
          PP ^ 2 * ((X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) := by ring
    rw [e]
    linarith
  unfold SumDat.total
  calc X.d * PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) +
        X.d * PP ^ 3 * X.T
      = X.d * (PP ^ 2 * (X.D ^ 3 * X.κ / X.T + X.T * X.c + (X.RR ^ 2 * X.c + 1 / X.T) * X.κ / X.γ₀) +
        PP ^ 3 * X.T) := by ring
    _ ≤ X.d * (X.f * m * b * δ₂) := mul_le_mul_of_nonneg_left hsum d0
    _ = X.d * X.f * m * b * δ₂ := by ring

theorem Ok.sum_le_page (h : X.Ok) {PP C k b m δ₂ q DF : ℝ} (hP : X.Rel PP)
    (hp : X.Page PP C k b m δ₂ q DF) :
    ∑ la ∈ X.s, X.rr la * X.l la ≤ X.d * X.f * m * b * δ₂ := (h.sum_le_total hP).trans (h.total_le_page hp)

theorem Ok.tsum_le_page (h : X.Ok) {PP C k b m δ₂ q DF : ℝ} (hP : X.Rel PP)
    (hp : X.Page PP C k b m δ₂ q DF) (h0 : ∀ la ∉ X.s, X.rr la * X.l la = 0) :
    Summable (fun la => X.rr la * X.l la) ∧ ∑' la, X.rr la * X.l la ≤ X.d * X.f * m * b * δ₂ := by
  refine ⟨summable_of_ne_finset_zero h0, ?_⟩
  rw [tsum_eq_sum h0]
  exact h.sum_le_page hP hp

theorem rr_nonneg (X : SumDat ι) (la : ι) (h1 : 0 ≤ X.R * X.I la)
    (h2 : 0 ≤ X.R * (X.T * (X.c / (2 * X.i)) * X.N la)) (h3 : 0 ≤ X.cD la)
    (h4 : 0 ≤ X.vQ la + X.ρ' * X.be la) : 0 ≤ X.rr la := by
  unfold SumDat.rr
  rw [mul_add]
  linarith

end SumDat

theorem share_of_div {ρ' d x : ℝ} (hd : 0 < d) (h : ρ' / d ≤ x) : ρ' ≤ d * x := by
  rw [div_le_iff₀ hd] at h
  linarith

theorem add_half_le_mul {lrw Prw L : ℝ} (h : lrw ≤ Prw * (L - 1)) (hP : 1 / 2 ≤ Prw) :
    lrw + 1 / 2 ≤ Prw * L := by linarith

theorem log_delta_le {R δ d Pd : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hRδ : R * δ ≤ d) (hd : Real.log d ≤ Pd) :
    Real.log δ ≤ Pd := by
  have hδd : δ ≤ d := by nlinarith
  exact (Real.log_le_log hδ hδd).trans hd

theorem mul_le_two_mul_of_eq {κ F' T L : ℝ} (h : κ = F' + T * L - T) (hF : 0 ≤ F') (hT : T ≤ κ) :
    T * L ≤ 2 * κ := by linarith

theorem deep_norm {κ F' F0 T D L : ℝ} (h : κ = F' + T * L - T) (h0 : F0 = F' + D * L - D) :
    (T - D) * L + F0 = κ + T - D := by linear_combination h0 - h

theorem Hdel_le {HL Hδ δ D G PH PI4 Prw L aG1 w : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hw0 : 0 ≤ w) (hw : w ≤ Prw * L) (hP : PI4 + Prw ≤ PH)
    (ha : aG1 ≤ 4 / 3 * δ) (hHL : HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L)
    (hH : Hδ ≤ HL + (δ * PI4 * D * L + D * aG1 * w)) :
    Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L := by
  have e1 : aG1 * w ≤ 4 / 3 * δ * (Prw * L) :=
    (mul_le_mul_of_nonneg_right ha hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have e2 := mul_le_mul_of_nonneg_left e1 hD
  have e3 : D * aG1 * w = D * (aG1 * w) := by ring
  have q1 : 0 ≤ δ * D * L * (PH - PI4 - Prw) := mul_nonneg (by positivity) (by linarith)
  have q2 : 0 ≤ δ * D * L * PI4 := by positivity
  have q3 : 0 ≤ δ * D * L * Prw := by positivity
  have q4 : 0 ≤ δ * L * PH := mul_nonneg (by positivity) (by linarith)
  linarith

theorem HF_le {HL HF δ D G PH PI4 Prw L aG2 w : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hw0 : 0 ≤ w) (hw : w ≤ Prw * L) (hP : PI4 + Prw ≤ PH)
    (ha : aG2 ≤ 4 / 3 * (D + 4) * δ) (hHL : HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L)
    (hH : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * w) :
    HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L := by
  have e1 : aG2 * w ≤ 4 / 3 * (D + 4) * δ * (Prw * L) :=
    (mul_le_mul_of_nonneg_right ha hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have e2 := mul_le_mul_of_nonneg_left e1 hD
  have e3 : D * aG2 * w = D * (aG2 * w) := by ring
  have e4 : (D + 4) * HL ≤ (D + 4) * ((D + 1) * δ * (2 * G + 4 * PH) * L) :=
    mul_le_mul_of_nonneg_left hHL (by positivity)
  have q0 : 0 ≤ δ * L * (D + 4) * (D + 1) * (PH - PI4 - Prw) := mul_nonneg (by positivity) (by linarith)
  have q1 : 0 ≤ δ * L * PI4 * D ^ 2 := by positivity
  have q2 : 0 ≤ δ * L * PI4 * D := by positivity
  have q3 : 0 ≤ δ * L * PI4 := by positivity
  have q4 : 0 ≤ δ * L * Prw * D ^ 2 := by positivity
  have q5 : 0 ≤ δ * L * Prw * D := by positivity
  have q6 : 0 ≤ δ * L * Prw := by positivity
  linarith

theorem deep_size {T D ΛW Λ0 lrw A E G Prw tableDegreeThreeBase PE L F0 κ : ℝ} (hD : 0 ≤ D) (hDT : D ≤ T) (hG : 0 ≤ G)
    (hPrw : 0 ≤ Prw) (hPE : 0 ≤ PE) (hF0 : 0 ≤ F0) (hκ : 1 ≤ κ) (hTκ : T ≤ κ)
    (hW : ΛW ≤ G * L) (h0 : Λ0 ≤ G * F0) (hrw : lrw ≤ Prw * (L - 1))
    (hn : (T - D) * L + F0 = κ + T - D) (hA : A ≤ tableDegreeThreeBase * κ) (hE : E ≤ PE) :
    (T - D) * (ΛW + lrw) + Λ0 + A + E ≤ (2 * G + Prw + tableDegreeThreeBase + PE) * κ := by
  have hTD : 0 ≤ T - D := by linarith
  have e1 : (T - D) * ΛW ≤ (T - D) * (G * L) := mul_le_mul_of_nonneg_left hW hTD
  have e2 : (T - D) * lrw ≤ (T - D) * (Prw * (L - 1)) := mul_le_mul_of_nonneg_left hrw hTD
  have e3 : G * (κ + T - D) ≤ G * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) hG
  have e4 : G * ((T - D) * L + F0) = G * (κ + T - D) := by rw [hn]
  have e5 : Prw * ((T - D) * L + F0) = Prw * (κ + T - D) := by rw [hn]
  have e6 : 0 ≤ Prw * F0 := mul_nonneg hPrw hF0
  have e7 : PE ≤ PE * κ := le_mul_of_one_le_right hPE hκ
  linarith

theorem deep_E {ld ln lr Pd PO : ℝ} (hPd : 0 ≤ Pd) (h1 : ld ≤ Pd) (h2 : ln ≤ PO) (h3 : lr ≤ PO) :
    ld + 1 / 2 * ln + lr ≤ 3 / 2 * (Pd + PO) := by linarith

theorem SumDat.rel_of_abs {ι : Type*} (X : SumDat ι) {CP Z PP : ℝ} (hCP : 1 ≤ CP) (hZ : 2 ≤ Z)
    (hPP : PP = CP * Z ^ 12) (hD : 1 ≤ X.D) (h1 : X.P1 ≤ CP * Z ^ 6) (h2 : X.P2 ≤ CP * Z ^ 5)
    (h3 : X.P3 ≤ CP * Z ^ 3) (h4 : X.P4 ≤ 2 * (CP * Z ^ 10) * (CP * Z ^ 4)) : X.Rel PP := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hCP0 : 0 ≤ CP := by linarith
  have hPP2 : PP ^ 2 = CP ^ 2 * Z ^ 24 := by rw [hPP]; ring
  have hPP3 : PP ^ 3 = CP ^ 3 * Z ^ 36 := by rw [hPP]; ring
  have cp2 : CP ≤ CP ^ 2 := le_self_pow₀ hCP (by norm_num)
  have cp3 : CP ≤ CP ^ 3 := le_self_pow₀ hCP (by norm_num)
  have z6 : Z ^ 6 ≤ Z ^ 24 := pow_le_pow_right₀ hZ1 (by norm_num)
  have z5 : Z ^ 5 ≤ Z ^ 36 := pow_le_pow_right₀ hZ1 (by norm_num)
  have z3 : Z ^ 3 ≤ Z ^ 24 := pow_le_pow_right₀ hZ1 (by norm_num)
  have z14 : 2 * Z ^ 14 ≤ Z ^ 24 := by
    have a : (2 : ℝ) ≤ Z ^ 10 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hZ 10)
    calc 2 * Z ^ 14 ≤ Z ^ 10 * Z ^ 14 := mul_le_mul_of_nonneg_right a (by positivity)
      _ = Z ^ 24 := by ring
  have r1 : X.P1 * X.D ^ 2 ≤ PP ^ 2 * X.D ^ 3 := by
    have a : X.P1 ≤ PP ^ 2 :=
      h1.trans (by rw [hPP2]; exact mul_le_mul cp2 z6 (by positivity) (by positivity))
    have b : X.P1 * X.D ^ 2 ≤ PP ^ 2 * X.D ^ 2 := mul_le_mul_of_nonneg_right a (sq_nonneg _)
    have c : X.D ^ 2 ≤ X.D ^ 3 := pow_le_pow_right₀ hD (by norm_num)
    exact b.trans (mul_le_mul_of_nonneg_left c (sq_nonneg _))
  have r2 : X.P2 ≤ PP ^ 3 :=
    h2.trans (by rw [hPP3]; exact mul_le_mul cp3 z5 (by positivity) (by positivity))
  have r3 : X.P3 ≤ PP ^ 2 :=
    h3.trans (by rw [hPP2]; exact mul_le_mul cp2 z3 (by positivity) (by positivity))
  have r4 : X.P4 ≤ PP ^ 2 := by
    refine h4.trans ?_
    rw [hPP2, show 2 * (CP * Z ^ 10) * (CP * Z ^ 4) = CP ^ 2 * (2 * Z ^ 14) by ring]
    exact mul_le_mul_of_nonneg_left z14 (by positivity)
  exact ⟨r1, r2, r3, r4⟩

theorem HL_le {HL X8 Y HM δ D G PH tableDegreeThreeBase PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw L lrw ΛW Sν DF c cg aδ aG1 : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 1 ≤ L) (hG : 0 ≤ G) (hPP0 : 0 ≤ tableDegreeThreeBase) (hPN : 0 ≤ PN) (hP14 : 0 ≤ tableLineDegreeFive)
    (hP16 : 0 ≤ tableLineDegreeTwo) (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hlrw : 0 ≤ lrw) (hw : lrw + 1 / 2 ≤ Prw * L)
    (hPH : tableDegreeThreeBase + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw ≤ PH) (hc1 : c ≤ 1) (hcg0 : 0 ≤ cg) (hcg : cg ≤ 1 / 2)
    (hSν : Sν ≤ PN * L) (hDF : DF ≤ L) (hΛ : ΛW ≤ G * L) (haδ : aδ ≤ 4 / 3 * δ) (haG : aG1 ≤ 4 / 3 * δ)
    (hHM : HM ≤ (D + 1) * δ * (tableDegreeThreeBase * L + ΛW + 1 / 2 * lrw))
    (hX8 : X8 ≤ HM + δ * (Sν + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * cg * aδ * (lrw + 1 / 2))
    (hY : Y ≤ δ * PI4 * D * L + D * aG1 * (lrw + 1 / 2))
    (hHL : HL ≤ 2 * max X8 0 + Y) :
    HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L := by
  have hL0 : 0 ≤ L := by linarith
  have hw0 : 0 ≤ lrw + 1 / 2 := by linarith
  have b1 : HM ≤ (D + 1) * δ * (tableDegreeThreeBase * L + G * L + 1 / 2 * (Prw * L)) :=
    hHM.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have b2 : δ * (Sν + tableLineDegreeFive * DF + c * tableLineDegreeTwo) ≤ δ * (PN * L + tableLineDegreeFive * L + tableLineDegreeTwo * L) := by
    have i1 : tableLineDegreeFive * DF ≤ tableLineDegreeFive * L := mul_le_mul_of_nonneg_left hDF hP14
    have i2 : c * tableLineDegreeTwo ≤ 1 * tableLineDegreeTwo := mul_le_mul_of_nonneg_right hc1 hP16
    have i3 : tableLineDegreeTwo ≤ tableLineDegreeTwo * L := le_mul_of_one_le_right hP16 hL
    exact mul_le_mul_of_nonneg_left (by linarith) hδ
  have b3 : D * cg * aδ * (lrw + 1 / 2) ≤ D * (1 / 2 * (4 / 3 * δ) * (Prw * L)) := by
    have i1 : cg * aδ ≤ cg * (4 / 3 * δ) := mul_le_mul_of_nonneg_left haδ hcg0
    have i2 : cg * (4 / 3 * δ) ≤ 1 / 2 * (4 / 3 * δ) := mul_le_mul_of_nonneg_right hcg (by positivity)
    have i3 : cg * aδ * (lrw + 1 / 2) ≤ 1 / 2 * (4 / 3 * δ) * (lrw + 1 / 2) :=
      mul_le_mul_of_nonneg_right (i1.trans i2) hw0
    have i4 : 1 / 2 * (4 / 3 * δ) * (lrw + 1 / 2) ≤ 1 / 2 * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have i5 := mul_le_mul_of_nonneg_left (i3.trans i4) hD
    calc D * cg * aδ * (lrw + 1 / 2) = D * (cg * aδ * (lrw + 1 / 2)) := by ring
      _ ≤ _ := i5
  have b4 : Y ≤ δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)) := by
    have i1 : aG1 * (lrw + 1 / 2) ≤ 4 / 3 * δ * (lrw + 1 / 2) := mul_le_mul_of_nonneg_right haG hw0
    have i2 : 4 / 3 * δ * (lrw + 1 / 2) ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul_of_nonneg_left hw (by positivity)
    have i3 := mul_le_mul_of_nonneg_left (i1.trans i2) hD
    have e : D * aG1 * (lrw + 1 / 2) = D * (aG1 * (lrw + 1 / 2)) := by ring
    linarith
  have hX8b0 : 0 ≤ ((D + 1) * δ * (tableDegreeThreeBase * L + G * L + 1 / 2 * (Prw * L)) + δ * (PN * L + tableLineDegreeFive * L + tableLineDegreeTwo * L) + D * (1 / 2 * (4 / 3 * δ) * (Prw * L))) := by positivity
  have hmax : max X8 0 ≤ ((D + 1) * δ * (tableDegreeThreeBase * L + G * L + 1 / 2 * (Prw * L)) + δ * (PN * L + tableLineDegreeFive * L + tableLineDegreeTwo * L) + D * (1 / 2 * (4 / 3 * δ) * (Prw * L))) := max_le (by linarith) hX8b0
  have q0 : 0 ≤ δ * L * (D + 1) * (PH - (tableDegreeThreeBase + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw)) :=
    mul_nonneg (by positivity) (by linarith)
  have qa0 : 0 ≤ δ * L * tableDegreeThreeBase := by positivity
  have qb0 : 0 ≤ δ * L * tableDegreeThreeBase * D := by positivity
  have qa1 : 0 ≤ δ * L * PN := by positivity
  have qb1 : 0 ≤ δ * L * PN * D := by positivity
  have qa2 : 0 ≤ δ * L * tableLineDegreeFive := by positivity
  have qb2 : 0 ≤ δ * L * tableLineDegreeFive * D := by positivity
  have qa3 : 0 ≤ δ * L * tableLineDegreeTwo := by positivity
  have qb3 : 0 ≤ δ * L * tableLineDegreeTwo * D := by positivity
  have qa4 : 0 ≤ δ * L * PI4 := by positivity
  have qb4 : 0 ≤ δ * L * PI4 * D := by positivity
  have qa5 : 0 ≤ δ * L * Prw := by positivity
  have qb5 : 0 ≤ δ * L * Prw * D := by positivity
  linarith

end Formalism.MainNotions.Gaps.T0
