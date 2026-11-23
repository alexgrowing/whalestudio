import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

namespace UpperTheory.ComplexUniformization

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

def hatL (p : ℕ) [Fact p.Prime] (Λ : Type) [AddCommGroup Λ] : AddSubgroup (AfP p ⊗[ℚ] (ℚ ⊗[ℤ] Λ)) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : Λ), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)}

structure PreA {N : ℕ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} (L : Link D G) (β : G.Cˣ) (X : MP D N ρ) where

  j : X.Dl.La →+ VQ D
  j_inj : Function.Injective j
  j_span : Submodule.span ℚ (Set.range j) = ⊤
  j_lin : ∀ (c : D.O) z, j (c • z) = actQ D c (j z)

  c₀ : ℚ
  c₀_pos : 0 < c₀
  form : ∀ z z', c₀ * (X.Dl.EF z z' : ℚ) = 2 * D.EF.baseChange ℚ (L.rep (β⁻¹ : G.Cˣ) (j z)) (j z')

  g : (AfP p ⊗[ℚ] G.C)ˣ

  ν : (AfP p)ˣ
  ν_int : IsIntAf (ν : AfP p)
  ν_int' : IsIntAf ((ν⁻¹ : (AfP p)ˣ) : AfP p)
  sim : (starT G.star (AfP p) (g : AfP p ⊗[ℚ] G.C)).unop * inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C) * (g : AfP p ⊗[ℚ] G.C) =
    algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) c₀ * (ν : AfP p))
  lat : latAf (Set.range j) = (LaHat D).map (actAf L g).toAddMonoidHom
  mark : ∀ l : D.La, ∃ w ∈ latAf (Set.range j), actAf L g (inAf D l) = (1 : AfP p) ⊗ₜ j (X.t l) + N • w

structure PreR {N : ℕ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} (L : Link D G) (v : InfinitePlace G.F) (β : G.Cˣ)
    (X : MP D N ρ) (j : X.Dl.La →+ VQ D) where

  Pq : VQ D →ₗ[ℚ] (Fin D.g → ℂ)
  Pq_j : ∀ z, Pq (j z) = X.P z

  Jc : ℝ ⊗[ℚ] G.C
  J_eq : ∀ u : ℝ ⊗[ℚ] VQ D, LinearMap.liftBaseChange ℝ Pq (actOn L.rep ℝ Jc u) =
    Complex.I • LinearMap.liftBaseChange ℝ Pq u

  z : Fin G.n → ℂ
  line : G.psiR v Jc *ᵥ z = (if v.embedding (L.e D.ω) = D.ρc then Complex.I else -Complex.I) • z
  pos : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re

end UpperTheory.ComplexUniformization
