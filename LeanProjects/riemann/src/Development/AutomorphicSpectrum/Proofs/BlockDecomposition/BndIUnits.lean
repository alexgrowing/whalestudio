import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2Factorization

abbrev rp (a : Jd) : ℝˣ := RationalIdeles.realPart a

def rI (W : GL (Fin 3) ℝ → ℂ) (W' : GL (Fin 2) ℝ → ℂ) (s : ℂ) (a b : ℝˣ) (k : GL (Fin 2) ℝ) : ℂ :=
  W (GL2LocalData.emR (dg2 (a * b) b * k)) * W' (dg2 (a * b) b * k) * chR false (s - 3 / 2) a * chR false (2 * s - 1) b

def pureInt (R : ℝˣ → ℝˣ → GL (Fin 2) ℝ → ℂ)
    (F : ∀ v : Pl, (Qv v)ˣ × (Qv v)ˣ × GL (Fin 2) (Qv v) → ℂ) (a z : Jd) (κ : KA) : ℂ :=
  R (rp a) (rp z) (GroundTheory.Automorphic.GL2Classical.realPart κ.1) * ∏ᶠ v, F v (lc v a, lc v z, finAt v κ.1)

structure FG {v : Pl} (W : GL (Fin 3) (Qv v) → ℂ) : Prop where
  smooth : ∃ U : OpenSubgroup (GL (Fin 3) (Qv v)), ∀ g, ∀ u ∈ U, W (g * u) = W g
  gauge : ∃ (C B : ℝ) (T : ℕ), ∀ (a b : (Qv v)ˣ), ∀ k ∈ integralGL (Qv v) 3,
    ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((modulus (a : Qv v) : ℝ) * modulus (b : Qv v)) ^ T ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : Qv v) : ℝ) ≤ B ∧ (modulus (b : Qv v) : ℝ) ≤ B)

structure ThG {v : Pl} (W : GL (Fin 2) (Qv v) → ℂ) : Prop where
  smooth : ∃ U : OpenSubgroup (GL (Fin 2) (Qv v)), ∀ g, ∀ u ∈ U, W (g * u) = W g
  gauge : ∃ (C : ℝ) (N : ℕ), ∀ (a b : (Qv v)ˣ), ∀ k ∈ integralGL (Qv v) 2,
    ‖W (dg2 (a * b) b * k)‖ ≤ C * (((modulus (a : Qv v) : ℝ) + (modulus (a : Qv v) : ℝ)⁻¹) *
      ((modulus (b : Qv v) : ℝ) + (modulus (b : Qv v) : ℝ)⁻¹)) ^ N

structure LocI (v : Pl) (F : (Qv v)ˣ × (Qv v)ˣ × GL (Fin 2) (Qv v) → ℂ) : Prop where
  int : Integrable F (GL2LocalData.mIw (GP.psiF v))
  lc : IsLocallyConstant F
  right : ∃ U : OpenSubgroup (GL (Fin 2) (Qv v)), ∀ a b k, ∀ u ∈ U, F (a, b, k * u) = F (a, b, k)

structure UnrI (v : Pl) (F : (Qv v)ˣ × (Qv v)ˣ × GL (Fin 2) (Qv v) → ℂ) : Prop where
  inv : ∀ a b u u' : (Qv v)ˣ, ord (u : Qv v) = 0 → ord (u' : Qv v) = 0 → ∀ k ∈ integralGL (Qv v) 2,
    F (a * u, b * u', k) = F (a, b, 1)
  one : F (1, 1, 1) = 1

structure BndI (σ : ℝ) (v : Pl) (F : (Qv v)ˣ × (Qv v)ˣ × GL (Fin 2) (Qv v) → ℂ) : Prop where
  supp : ∀ a b : (Qv v)ˣ, F (a, b, 1) ≠ 0 → (a : Qv v) ∈ 𝒪[Qv v] ∧ (b : Qv v) ∈ 𝒪[Qv v]
  bound : ∀ m n : ℕ, ‖F (unifUnit (Qv v) ^ m, unifUnit (Qv v) ^ n, 1)‖ ≤
    (((m : ℝ) + 1) * ((n : ℝ) + 1)) ^ 2 * (pOf v : ℝ) ^ (-(((m : ℝ) + n) * σ))

def SphF {v : Pl} (W : GL (Fin 3) (Qv v) → ℂ) : Prop :=
  (∀ k ∈ integralGL (Qv v) 3, ∀ g, W (g * k) = W g) ∧ W 1 = 1

end GlobalTheory.CompanionTheory.GL2Factorization
