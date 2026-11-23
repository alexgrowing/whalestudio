import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU

variable {p : ℕ} [Fact p.Prime]

def Datum.inv (D : Datum p) (x : D.O) : D.O := (D.star x).unop

def Datum.plat (D : Datum p) : PLat D.O D.inv where
  La := D.La
  fin := D.finLa
  free := D.freeLa
  EF := (2 : ℤ) • D.EF
  alt x := by simp [D.alt]
  nondeg x h := D.nondeg (by
    ext y
    have := h y
    simpa using this)
  adj a x y := by simp [D.adj, Datum.inv]

def Datum.g (D : Datum p) : ℕ := D.m * D.n * Module.finrank ℚ D.F / 2

def HalfPerf {O : Type} [Ring O] {bar : O → O} (p : ℕ) (D' : PLat O bar) : Prop :=
  ∃ E₁ : LinearMap.BilinForm ℤ D'.La, D'.EF = (2 : ℤ) • E₁ ∧
    ∃ e : ℕ, e.Coprime p ∧ ∀ f : D'.La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e • f

def Datum.Cls (D : Datum p) (N : ℕ) (D' : PLat D.O D.inv) (t : D.La → D'.La) : Prop :=
  Genus p N D.plat D' t ∧ HalfPerf p D'

open Classical in

def Base.IsType {D : Datum p} {R : Type} [CommRing R] (b : Base D R) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, σ (b.t i c) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ σ b.ρ), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (σ (b.t i c)))

def Base.Matches {D : Datum p} {R : Type} [CommRing R] (b : Base D R) (σ : R →+* ℂ) : Prop :=
  σ b.ρ = D.ρc ∧ ∀ i (c : 𝓞 D.F), σ (b.t i c) = D.tau i (c : D.F)

def Obj.fam {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) :
    Fam R D.O D.La D.g where
  X := S
  s := s
  A := o.A
  ab := o.ab
  dim := h
  act := o.act.act
  hom := o.act.hom
  act_one := o.act.one
  act_mul := o.act.mul
  act_add := o.act.add
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  isLB := hL
  ample := o.ample
  eta := o.eta

def Model.Uniformised {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} (M : Model b N) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∃ h hL, Nonempty (Unif (M.univ.fam h hL) σ ρ N (D.Cls N))

end GlobalTheory.UPel.HT
