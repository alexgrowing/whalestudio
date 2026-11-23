import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Le (B A : HermLB p) : Prop :=
  ∃ P : Pair p, P.L = A ∧ P.A = B ∧ (1 : X.functionField) ∈ P.Bl 1 (-1) 1

omit [IsIntegral X] in

def HtNef (M : HermLB p) (D : ℕ) : Prop :=
  M.SemiPos D ∧ ∀ h : X → ℝ, M.IsArithHeight h → ∀ x, 0 ≤ h x

def Total {J : Type} (f : J → X.functionField) : Prop :=
  (∀ j, f j ≠ 0) ∧ ∀ (x : X) (j l : J), RegAt x (f j / f l) ∨ RegAt x (f l / f j)

def SmallFam (B : HermLB p) {J : Type} (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ β : B.B.ι → X.functionFieldˣ, IsRatSec B.B β ∧
    (∀ (x : X) c, x ∈ B.B.U c → ∀ j, RegAt x (f j * (β c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (B.B.U c) → ∀ j,
      ‖ratVal (f j * (β c : X.functionField)) y‖ * Real.exp (-(B.φ σ).φ c y / 2) ≤ Real.exp (-w j)

def IsFS (M : HermLB p) {J : Type} [Fintype J] (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c, x ∈ M.B.U c → (∀ j, RegAt x (f j * (ρ c : X.functionField))) ∧ ∃ j, UnitAt x (f j * (ρ c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (M.B.U c) →
      (M.φ σ).φ c y = Real.log (∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j))

structure IsModel {Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField) : Prop where

  gen : π (genericPoint Y) = genericPoint X

  deg : π.residueDegree (genericPoint Y) = 1

  compat : ∀ (y : Y) (a : X.presheaf.stalk (π y)),
    φ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a)

def boxFam {K J : Type} [Field K] {D : ℕ} (e : J → K) (x : Fin D → K) : J × Finset (Fin D) → K :=
  fun c => e c.1 * ∏ i ∈ c.2, x i

def shiftA (P : Pair p) (u : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => u) fun _ => rfl, P.r, P.r', P.hr, P.hr'⟩

def GenAt (P : Pair p) (c : ℕ) : Prop :=
  ∃ (n : ℕ) (v : Fin n → X.functionField), (∀ i, v i ∈ P.H 0 c) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (v i) ≠ 0

def Regime (P : Pair p) (D : ℕ) : Prop :=
  ∃ α β : ℝ, ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun m : ℕ => P.lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + β * t))

def bound (D q : ℕ) (b g : ℝ) : ℝ :=
  let Δ := Real.log ((q : ℝ) / 2)
  let α := (b + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ)
  let β := (D + 1) * g / (2 * ((D + 1).factorial * Δ))
  Real.log q * (α + β * Real.log ((α + 2 * β + 1) ^ 2))

def AmpleHS : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a : ℝ), IsAmpleLB P.L.B → P.L.SemiPos D → P.L.IsSelfInter a →
      ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
        Tendsto (fun m : ℕ => P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
          (𝓝 ((a + ((D : ℝ) + 1) * t * gdeg P.L D) / ((D + 1).factorial : ℝ)))

def SemiPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E

theorem shiftA_H (P : Pair p) (u : ℝ) (a b : ℤ) : (shiftA P u).H a b = P.H a b := rfl

end GlobalTheory.HSNef
