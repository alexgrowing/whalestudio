import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwiner
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_plancherel_schrodinger_intertwiner_alt : ∀ {X Aψ G : Type} [AddCommGroup X] [AddCommGroup Aψ] [AddCommGroup G] [Fintype G]
  (ψ : AddChar Aψ ℂ) (B : X → X → Aψ) (Λc : AddSubgroup X) (red : Λc →+ G)
  (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hs : X → (X → ℂ) → (X → ℂ)) (SB : (X → ℂ) → Prop) (Hd : X → Prop)
  (Th : (X → ℂ) → Prop) (ip : (X → ℂ) → (X → ℂ) → ℂ) (f₀ : X → ℂ) (Gd : G → ℂ),
  Function.Surjective red →
  (∀ t k y, B (t + k) y = B t y + B k y) →
  (∀ Ψ : X → ℂ, (∀ t, Ψ t ≠ 0 → t ∈ Λc) → (∀ t, ∀ u ∈ Λc, Ψ (t + Fintype.card G • u) = Ψ t) → SB Ψ) →
  (∀ Φ, SB Φ → ∀ x ∈ Λc, T (fun t => Φ (t + x)) = hs x (T Φ)) →
  (∀ Φ, SB Φ → ∀ y, Hd y → T (fun t => ψ (B t y) * Φ t) = hs y (T Φ)) →
  T (fun t => if t ∈ Λc then 1 else 0) = f₀ →
  (∀ x : Λc, red x ≠ 0 → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ ψ (B x y) ≠ 1) →
  (∀ w (a : ℂ) (f₁ f₂ : X → ℂ), hs w (a • f₁ + f₂) = a • hs w f₁ + hs w f₂) →
  (∀ (a : ℂ) f₁ f₂, Th f₁ → Th f₂ → Th (a • f₁ + f₂)) →
  (∀ w f, Th f → Th (hs w f)) →
  (∀ (a : ℂ) f₁ f₂ g, Th f₁ → Th f₂ → Th g → ip (a • f₁ + f₂) g = a * ip f₁ g + ip f₂ g) →
  (∀ f g, Th f → Th g → ip g f = starRingEnd ℂ (ip f g)) →
  (∀ w f₁ f₂, Th f₁ → Th f₂ → ip (hs w f₁) (hs w f₂) = ip f₁ f₂) →
  Th f₀ → ip f₀ f₀ = 1 →
  ip (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) =
    ((∑ g, ‖Gd g‖ ^ 2 : ℝ) : ℂ) / (Fintype.card G : ℂ) := by
  first | exact @GlobalTheory.finite_plancherel_schrodinger_intertwiner | exact GlobalTheory.finite_plancherel_schrodinger_intertwiner | (intros; apply GlobalTheory.finite_plancherel_schrodinger_intertwiner <;> assumption)
