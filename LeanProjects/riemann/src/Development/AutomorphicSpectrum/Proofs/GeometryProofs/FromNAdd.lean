import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F]

abbrev NAdd (E : Type) [Field E] [NumberField E] (n p : ℕ) : Type := Fin n → (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})

def toNAdd {n p : ℕ} (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : (Fin n → F) →+ NAdd E n p where
  toFun a i := sc (a i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def fromNAdd {n p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) : NAdd E n p →+ (Fin n → F) where
  toFun t i := pq (t i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def bcLin (C : Type) [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω)) :
    (Fin m → C) →ₗ[C] (Fin n → C) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap Ω C))

variable {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

def testOrd (P : ChartPack G O c') {C : Type} [Field C] [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) :
    Submodule RC (NAdd E (D.p + D.q) p → C) :=
  Submodule.span RC {f | ∃ g ∈ P.Γ₁.btOrder ⊤, f = fun x =>
    algebraMap Ω C ((g (Multiplicative.ofAdd x) : CR O y c') : Ω)}

def testOrdW (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {C : Type} [Field C] [Algebra O C]
    [Algebra Ω C] (RC : Subalgebra O C) : Submodule RC ((Fin (D.p + D.q) → F) → C) :=
  (testOrd P RC).map (LinearMap.funLeft RC C (toNAdd sc : (Fin (D.p + D.q) → F) → NAdd E (D.p + D.q) p))

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
