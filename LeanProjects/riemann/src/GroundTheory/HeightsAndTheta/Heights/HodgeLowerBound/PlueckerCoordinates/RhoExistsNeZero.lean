import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure RegData (P : Ideal (MRing ι)) (d : ℕ) (Bd : Set ((Σ k, ι k) → ℂ)) where

  nc : ℕ

  chart : Fin nc → SncChart P d Bd

  r1 : ℝ

  r3 : ℝ

  r2 : ℝ
  r1_pos : 0 < r1
  r1_lt_r3 : r1 < r3
  r3_lt_r2 : r3 < r2
  r2_lt_one : r2 < 1
  cover : ∀ z ∈ mcPts P, ∃ a, ∃ t : Fin d → ℂ, ‖t‖ ≤ r1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
    z = torusSmul c ((chart a).γ t)

  eta : Fin nc → (Fin d → ℂ) → ℝ
  eta_smooth : ∀ a, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eta a)
  eta_le : ∀ a t, eta a t ≤ 0
  le_eta : ∀ a t, -1 ≤ eta a t
  eta_inner : ∀ a t, ‖t‖ ≤ r1 → eta a t = 0
  eta_outer : ∀ a t, r3 ≤ ‖t‖ → eta a t = -1

  rho : ℝ → ℝ
  rho_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho
  rho_nonneg : ∀ s, 0 ≤ rho s
  rho_supp : ∀ s, rho s ≠ 0 → 1 / 2 ≤ s ∧ s ≤ 1
  rho_ne : ∃ s, rho s ≠ 0

  rho0 : ℝ → ℝ
  rho_contDiff_alt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho0
  rho_nonneg_alt : ∀ s, 0 ≤ rho0 s
  rho_even : ∀ s, rho0 (-s) = rho0 s
  rho_support_half : ∀ s, rho0 s ≠ 0 → |s| ≤ 1 / 2
  rho_exists_ne_zero : ∃ s, rho0 s ≠ 0

  Ce : ℝ
  Ce_pos : 0 < Ce

namespace RegData

variable {P : Ideal (MRing ι)} {d : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} (R : RegData P d Bd)

def InChart (a : Fin R.nc) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ t : Fin d → ℂ, ‖t‖ < R.r2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((R.chart a).γ t)

open Classical in

def coord (a : Fin R.nc) (z : (Σ k, ι k) → ℂ) : Fin d → ℂ :=
  if h : R.InChart a z then h.choose else 0

open Classical in

def active (z : (Σ k, ι k) → ℂ) : Finset (Fin R.nc) :=
  Finset.univ.filter fun a => R.InChart a z

def massRho : ℝ := ∫ x : ℂ, R.rho ‖x‖

def molli (t : ℝ) (ξ : Fin d → ℂ) : ℝ := ∏ i, R.rho (‖ξ i‖ / t) / (t ^ 2 * R.massRho)

def mollify (u : (Fin d → ℂ) → ℝ) (t : ℝ) (x : Fin d → ℂ) : ℝ :=
  ∫ ξ, u (x - ξ) * R.molli t ξ

def ell (t : ℝ) : ℝ := Real.log (1 / t)

def e1 (t : ℝ) : ℝ := R.Ce * (Real.log (ell t) / ell t + t)

def massRho0 : ℝ := ∫ s, R.rho0 s

def regMax (et : ℝ) (A : Finset (Fin R.nc)) (x : Fin R.nc → ℝ) : ℝ :=
  (∫ h : Fin R.nc → ℝ, (⨆ i : A, x i + et * h i) * ∏ i, R.rho0 (h i) / R.massRho0) + et / 2

def localReg (φ φ0 : ((Σ k, ι k) → ℂ) → ℝ) (a : Fin R.nc) (t : ℝ) (x : Fin d → ℂ) : ℝ :=
  R.mollify (fun x' => φ ((R.chart a).γ x')) t x - φ0 ((R.chart a).γ x)

def regDiff (φ φ0 : ((Σ k, ι k) → ℂ) → ℝ) (t : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  R.regMax (R.e1 t) (R.active z) fun a =>
    R.localReg φ φ0 a t (R.coord a z) + 4 * R.e1 t * R.eta a (R.coord a z)

def regWeight (φ φ0 : ((Σ k, ι k) → ℂ) → ℝ) (t : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  φ0 z + R.regDiff φ φ0 t z

end RegData

def IsSmoothExt (P : Ideal (MRing ι)) (f F : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
    (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → F (torusSmul c z) = F z) ∧ ∀ z ∈ mcPts P, F z = f z

open Classical in

def smoothExt (P : Ideal (MRing ι)) (f : ((Σ k, ι k) → ℂ) → ℝ) : ((Σ k, ι k) → ℂ) → ℝ :=
  if h : ∃ F, IsSmoothExt P f F then h.choose else fun _ => 0

theorem smoothExt_torus (P : Ideal (MRing ι)) (f : ((Σ k, ι k) → ℂ) → ℝ) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) : smoothExt P f (torusSmul c z) = smoothExt P f z := by
  classical
  unfold smoothExt
  split_ifs with h
  · exact h.choose_spec.2.1 c z hc
  · rfl

def twistLine (P : Ideal (MRing ι)) (A0 : HermLine ι) (f : ((Σ k, ι k) → ℂ) → ℝ) : HermLine ι where
  a := A0.a
  h z := A0.h z * Real.exp (smoothExt P f z)
  pos z hz := mul_pos (A0.pos z hz) (Real.exp_pos _)
  smul c z hc := by
    have h1 := smoothExt_torus P f c hc z
    have h2 := A0.smul c z hc
    rw [show (fun p => c p.1 * z p) = torusSmul c z from rfl] at h2 ⊢
    rw [h1, h2]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
