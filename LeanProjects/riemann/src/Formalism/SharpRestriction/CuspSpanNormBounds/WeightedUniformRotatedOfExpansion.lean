import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

noncomputable section

open Finset

namespace Formalism.MainNotions.RotatedPoints

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.S.Pv.Frames

section R

variable (D : D7)

def JSqR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) : ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))

def BSumR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSqR D X γ.1

def FirstBoundRotated (Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    BSumR D X (fun _ => 1) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def theoremBRotated (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumR D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def OnePlaceR (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (A : ℕ) (CK : ℝ) (e : ℕ)
    (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
        orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
      ENNReal.ofReal (b ^ (CK * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) * jNorm2 (X.L v) (X.f v) (X.μsec v)

variable {D}

theorem weighted_bound_rotated_of_one_place {Aw Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : OnePlaceR D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A CK 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) : theoremBRotated D Aw Ch Cg (CK + 6) := by
  exact Formalism.MainNotions.BesselShellMomentBounds.theorem_B_weighted_bound_one_place (D := D) hCg hO

variable (D)

def PlaceOKR (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D) ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec ∧
    Tz D.R.k D.R.rS L.z = T ∧ Tz D.R.k D.R.rS L.z' = T'

def BpRealR (Ch Cg dist : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOKR D Ch Cg T T' b dist v L f μsec →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ →
      ENNReal.ofReal (nLoc D T T' v γ) * orbSq L f (turnPt (ptLoc D v γ)) ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) *
          jNorm2 L f μsec

def QExpAtR (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (dist' : ℝ) (A : ℕ) (C : ℝ)
    (e : ℕ) (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ∃ (n : ℕ) (a : Fin n → ℝ) (L' : Fin n → LocBessel D.R.k D.R.rS)
      (f' : ∀ i, Mx D.R.k D.R.rS → ((L' i).Wq →L[ℂ] (L' i).Wp))
      (μ' : Fin n → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ),
      (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) ∧
      (∀ i, PlaceOKR D Ch Cg T T' b dist' v (L' i) (f' i) (μ' i)) ∧
      (∀ i, jNorm2 (L' i) (f' i) (μ' i) ≤ jNorm2 (X.L v) (X.f v) (X.μsec v)) ∧
      ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
          orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
        (∑ i, ENNReal.ofReal (a i) *
          (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2)) ^ 2

variable {D}

theorem sqrt_sq_enn (x : ENNReal) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem b_pos_of_dataR {Ch Cg dist : ℝ} {T T' : ℕ} {b : ℝ} (hCg : 2 ≤ Cg) (X : BData D Ch Cg T T' b dist)
    (v : D.what₂.Tau) : 0 < b := by
  obtain ⟨hk, -, -, -, -, hS, -⟩ := X.hL v
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlam, -, -, hgap, -⟩ := hS
  have hn : 1 < 2 * D.R.rS + D.R.k + 1 := by omega
  have h01 : (⟨0, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) ≠ ⟨1, hn⟩ := by simp [Fin.ext_iff]
  have hg := hgap _ _ h01
  have h1 := hlam ⟨0, by omega⟩
  have h2 := hlam ⟨1, hn⟩
  have h3 := norm_sub_le (lamSH D.R (D.hc v) ⟨0, by omega⟩) (lamSH D.R (D.hc v) ⟨1, hn⟩)
  simp only [Real.norm_eq_abs] at h3
  have hpos : 0 < Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := by
    have : (0 : ℝ) < ((2 * D.R.rS + 2 : ℕ) : ℝ) := by positivity
    positivity
  linarith

theorem onePlaceR_of_exp {Ch Cg dist dist' C1 C2 p : ℝ} {A e : ℕ} {P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop}
    (hCg : 2 ≤ Cg) (hQ : QExpAtR D Ch Cg dist P dist' A C1 e p) (hB : BpRealR D Ch Cg dist' A C2 e) :
    OnePlaceR D Ch Cg dist P A (2 * C1 + C2) e p := by
  intro T T' b X hP γ hγ v
  obtain ⟨n, a, L', f', μ', ha0, hasum, hok, hjn, hle⟩ := hQ T T' b X hP γ hγ v
  have hb : 0 < b := b_pos_of_dataR hCg X v
  set s : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e with hs
  set Mx : ℝ := max 1 (1 / absV D v (Gglob D T T' γ)) ^ A with hMx
  set K : ENNReal := ENNReal.ofReal (b ^ (C2 * s) * Mx) * jNorm2 (X.L v) (X.f v) (X.μsec v) with hK
  have hi : ∀ i, ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ)) ≤ K := by
    intro i
    refine (hB T T' b v (L' i) (f' i) (μ' i) (hok i) γ hγ).trans ?_
    rw [hK]
    gcongr
    exact hjn i
  have hsa : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha0 i
  have hsum : (∑ i, ENNReal.ofReal (a i) *
        (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2)) ≤
      ENNReal.ofReal (∑ i, a i) * K ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha0 i), Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    gcongr
    exact hi i
  refine hle.trans ?_
  calc (∑ i, ENNReal.ofReal (a i) *
        (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2)) ^ 2
      ≤ (ENNReal.ofReal (∑ i, a i) * K ^ ((1 : ℝ) / 2)) ^ 2 := by gcongr
    _ = ENNReal.ofReal (∑ i, a i) ^ 2 * K := by rw [mul_pow, sqrt_sq_enn]
    _ ≤ ENNReal.ofReal ((b ^ (C1 * s)) ^ 2) * K := by
        gcongr
        rw [← ENNReal.ofReal_pow hsa]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hsa hasum 2)
    _ = ENNReal.ofReal (b ^ ((2 * C1 + C2) * s) * Mx) * jNorm2 (X.L v) (X.f v) (X.μsec v) := by
        have e1 : (b ^ (C1 * s)) ^ 2 * (b ^ (C2 * s) * Mx) = b ^ ((2 * C1 + C2) * s) * Mx := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le, ← mul_assoc, ← Real.rpow_add hb]
          congr 2
          push_cast
          ring
        rw [hK, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), e1]

theorem weighted_bound_rotated_of_expansion {Aw Ch Cg dist' C1 C2 : ℝ} {A : ℕ} (hCg : 2 ≤ Cg) (_hAw : 0 ≤ Aw)
    (hQ : QExpAtR D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist' A C1 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2))
    (hB : BpRealR D Ch Cg dist' A C2 5) :
    theoremBRotated D Aw Ch Cg (2 * C1 + C2 + 6) := by
  exact weighted_bound_rotated_of_one_place hCg (onePlaceR_of_exp hCg hQ hB)

end R

def WeightedBoundRotatedUniform : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, theoremBRotated D Aw Ch Cg Cb

def WeightedExpansionRotated : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 dist' : ℝ) (A : ℕ) (Cg₀ : ℝ), 2 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    QExpAtR D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist' A C1 5
        (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
      BpRealR D Ch Cg dist' A C2 5

theorem weighted_uniform_rotated_of_expansion (h : WeightedExpansionRotated) : WeightedBoundRotatedUniform := by
  intro Aw Ch hAw
  obtain ⟨C1, C2, dist', A, Cg₀, hCg₀, hall⟩ := h Aw Ch hAw
  refine ⟨2 * C1 + C2 + 6, Cg₀, fun Cg hCg D => ?_⟩
  obtain ⟨hQ, hB⟩ := hall Cg hCg D
  exact weighted_bound_rotated_of_expansion (le_trans hCg₀ hCg) hAw hQ hB

end Formalism.MainNotions.RotatedPoints
