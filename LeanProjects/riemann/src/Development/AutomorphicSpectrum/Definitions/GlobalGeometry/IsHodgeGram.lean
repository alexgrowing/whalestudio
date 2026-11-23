import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R]

def IsComb {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G))
    (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsEigVec {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    (v : epsAt x ⟶ G) : Prop :=
  IsTanAt G x v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsMul (τ a)) ≫ v.left

def IsEigFrame {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigVec act x τ (v i)) ∧ ∀ w, IsEigVec act x τ w → ∃! c : Fin n → R, IsComb c v w

def IsHodgeGram (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) {n : ℕ} (v : Fin n → (epsAt x ⟶ G))
    (Γ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ G.left) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (u : HolUnif Q.A Q.L Q.g)
    (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin n → Fin Q.g → ℂ),
    IsGrpPullback Q.A G x ψ ∧ LBIso (L.pull ψ) Q.L ∧ u.IsAH Hm χ ∧
      (∀ i, (v' i).left ≫ ψ = (v i).left ∧ u.IsDiff (W i) (v' i)) ∧ ∀ i j, Γ i j = Real.pi * hermForm Hm (W i) (W j)

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tauIn {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F :=
  ((τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E) :)

def sesq (D : Datum H) (x y : D.La) : E :=
  ∑ k, (D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k

def tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (z : Fin g → ℂ) : Fin g → ℂ :=
  open Classical in fun k => if ty k = τ then z k else 0

end GlobalTheory.CompanionTheory.Ar.Fl
