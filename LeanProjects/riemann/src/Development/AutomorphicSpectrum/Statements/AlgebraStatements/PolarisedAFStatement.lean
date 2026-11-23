import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix

def PolarisedAFStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ H : HodgeTateDatum p g v R O σ cp,
    let φ := algebraMap R C
    let AF := afLat p H.AA.carrier
    let H' : Set (Ix g → C) := {x | ∀ l ∈ AF, v (∑ i, φ (l i) * x i) ≤ 1}
    let hb : Matrix (Ix g) (Fin g) C := (((H.E.map (algebraMap ℤ_[p] R))ᵀ)⁻¹ * H.Htᵀ).map φ
    AF = Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) ∧
    (∀ l : Ix g → R, cp • l ∈ AF) ∧
    HasLen v R ((Ix g → R) ⧸ AF) (v (φ cp) ^ g) ∧
    HasLen v R (AFQuot p H.AA.carrier) (v (φ cp) ^ g) ∧
    (∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧ ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1) ∧
    (∀ x, (x ∈ H' ∧ H.Ht.map φ *ᵥ x = 0) ↔
      ∃ w : Fin g → C, (∀ k, v (w k) ≤ 1) ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧
    (∀ w : Fin g → C, (∀ k, v (w k) ≤ 1) → ∃ x ∈ H', H.Ht.map φ *ᵥ x = w) ∧
    GenAF p H.AA.carrier ⊥ ∧ IsTight v p H.AA.carrier

end GlobalTheory.CompanionTheory.Ar.GR
