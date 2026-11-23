import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

def IsLatBasis {g r : ℕ} (K : Set (Fin g → ℂ)) (b : Fin r → Fin g → ℂ) : Prop :=
  LinearIndependent ℝ b ∧ ∀ w, w ∈ K ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • b j

def IsLatFam {n g : ℕ} (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) : Prop :=
  IsOpen B ∧ (∀ b ∈ B, ∃ H : AddSubgroup (Fin g → ℂ), (H : Set (Fin g → ℂ)) = K b) ∧
    IsOpen {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} ∧
    ∀ b₀ ∈ B, ∀ w₀ ∈ K b₀, ∃ ζ : (Fin n → ℂ) → Fin g → ℂ, ζ b₀ = w₀ ∧ AnalyticAt ℂ ζ b₀ ∧
      ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

def IsExpAt (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop :=
  (∀ v w, e (v + w) = e v * e w) ∧
    (∀ w, ∃! v, IsTanAtG t y v ∧ IsDerivAt0 (fun u => (e u).left) w v) ∧
    ∀ v, IsTanAtG t y v → ∃! w, IsDerivAt0 (fun u => (e u).left) w v

end Exp

end GlobalTheory.ShFam.Hor.LogCh
