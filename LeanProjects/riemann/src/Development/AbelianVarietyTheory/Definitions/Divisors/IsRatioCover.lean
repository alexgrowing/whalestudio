import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

abbrev str (A : Over (Sp ℂ)) : A.left ⟶ Sp ℂ := A.hom ≫ 𝟙 _

variable {A : Over (Sp ℂ)} {g : ℕ} (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))

def pre (U : A.left.Opens) : Set (Fin g → ℂ) := {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}

def val (U : A.left.Opens) (b : Γ(A.left, U)) (z : Fin g → ℂ) : ℂ := valAt' (ex z).left U b

def IsReg (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ) : Prop :=
  ∃ b : Γ(A.left, U), ∀ z ∈ pre ex U, k z = val ex U b z

def IsEv (U : A.left.Opens) (z : Fin g → ℂ) (E : Ω[Sec (str A) U⁄ℂ] →ₗ[ℂ] ((Fin g → ℂ) →L[ℂ] ℂ)) : Prop :=
  ∀ a b : Sec (str A) U, E (a • D ℂ (Sec (str A) U) b) = val ex U a z • fderiv ℂ (val ex U b) z

open Classical in

def evForm (U : A.left.Opens) (z : Fin g → ℂ) : Ω[Sec (str A) U⁄ℂ] →ₗ[ℂ] ((Fin g → ℂ) →L[ℂ] ℂ) :=
  if h : ∃ E, IsEv ex U z E then h.choose else 0

def IsPrim (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (h : A.left.affineOpens → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ U : A.left.affineOpens, DifferentiableOn ℂ (h U) (pre ex U.1)) ∧
  (∀ (U V : A.left.affineOpens) (a : op U ⟶ op V), ∀ z ∈ pre ex V.1, h V z = h U z + val ex V.1 (c.1.1 (op U) (op V) a) z) ∧
  ∀ U : A.left.affineOpens, ∀ z ∈ pre ex U.1, fderiv ℂ (h U) z = evForm ex U.1 z (c.1.2 (op U))

def IsPer (Λ : Submodule ℤ (Fin g → ℂ)) (x : HH1 (str A)) (q : Λ → ℂ) : Prop :=
  ∃ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (h : A.left.affineOpens → (Fin g → ℂ) → ℂ), Hyp1.mk _ c = x ∧ IsPrim ex c h ∧
    ∀ (U : A.left.affineOpens) (l : Λ), ∀ z ∈ pre ex U.1, h U (z + l) = h U z + q l

def IsRatioCover {n : ℕ} (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)) : Prop :=
  (∀ k, IsAffineOpen (W k)) ∧ ⨆ k, W k = ⊤ ∧ (∀ k j, A.left.basicOpen (r k j) = W k ⊓ W j) ∧ (∀ k, r k k = 1) ∧
    ∀ k j l, ∀ z ∈ pre ex (W k), z ∈ pre ex (W j) → val ex (W k) (r k l) z = val ex (W k) (r k j) z * val ex (W j) (r j l) z

end GlobalTheory.CechPer
