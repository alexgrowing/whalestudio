import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def IsValues (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
    (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (MV : LieModel P.tK.G (𝟙 (Sp L)) V)
    {m : ℕ} (s : Fin m → 𝔐.Li) (sL : Fin m → V) : Prop :=
  ∀ k, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
    𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (s k) v ∧ (MV.pt (sL k)).left ≫ P.m.φ = v.left

def primeOf {L : Type} [Field L] [NumberField L] (v : FinitePlace L) : PrimeSpectrum (𝓞 L) :=
  ⟨v.maximalIdeal.asIdeal, v.maximalIdeal.isPrime⟩

end Defs

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
