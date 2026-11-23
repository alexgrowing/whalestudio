import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.FlagCell

def uniR {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun a b => if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem uniR_eq_uni {m : ℕ} (n : Low m → ℂ) : uniR n = uni n := rfl

theorem uniR_apply {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) (a b : Fin m) :
    uniR n a b = if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0 := rfl

theorem map_uniR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (n : Low m → R) :
    (uniR n).map f = uniR fun s => f (n s) := by
  ext a b
  simp only [Matrix.map_apply, uniR_apply]
  split_ifs <;> simp

def pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ} (e : Fin m → Γ(E, U))
    {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    Γ((Scheme.Modules.pullback π).obj E, V) :=
  ∑ l, M l j • pullbackSections π E hV (e l)

def Spans {X : Scheme.{0}} {F : X.Modules} {m : ℕ} (fl : Vert.Flag F m) (V : X.Opens)
    (v : Fin m → Γ(F, V)) : Prop :=
  ∀ l : Fin (m + 1), ∃ s : Fin l → Γ(fl.F l, V), IsFrame s ∧
    ∀ j, (fl.ι l).app V (s j) = v (Fin.castLE l.is_le j)

end GlobalTheory.FlagCell
