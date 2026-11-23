import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.ComplexUniformization

variable {p : ℕ} [Fact p.Prime]

structure MP (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) where

  Dl : PLat D.O D.inv

  t : D.La → Dl.La

  P : Dl.La →+ (Fin D.g → ℂ)
  cls : D.Cls N Dl t
  per : IsPeriod Dl ρ P

def MP.Rel {D : Datum p} {N : ℕ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} (X X' : MP D N ρ) : Prop :=
  ∃ (w : X.Dl.La ≃ₗ[D.O] X'.Dl.La) (h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)),
    IsMarkedIsom N X.Dl X'.Dl X.t X'.t w ∧ ∀ z, X'.P (w z) = h (X.P z)

def TypeAt (D : Datum p) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, D.tau i (c : D.F) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (D.tau i (c : D.F)))

abbrev VP (D : Datum p) : Type := ℚ_[p] ⊗[ℚ] VQ D

variable {D : Datum p} {G : HTGroup p}

def Up (L : Link D G) : Submodule ℚ_[p] (VP D) :=
  LinearMap.ker ((actQ D (algebraMap (𝓞 D.F) D.O D.ω)).baseChange ℚ_[p] - (L.ρp : ℚ_[p]) • LinearMap.id)

structure IsULat (L : Link D G) (Λ : AddSubgroup (Up L)) : Prop where
  int : ∀ (c : ℤ_[p]) (u : Up L), u ∈ Λ → ((c : ℚ_[p]) • u) ∈ Λ
  fg : ∃ S : Finset (Up L), Λ = AddSubgroup.closure {w | ∃ (c : ℤ_[p]), ∃ s ∈ S, w = (c : ℚ_[p]) • s}
  span : ∀ u : Up L, ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • u ∈ Λ
  stable : ∀ (c : D.O) (u u' : Up L), u ∈ Λ → (u' : VP D) = (actQ D c).baseChange ℚ_[p] u → u' ∈ Λ

structure PAct (L : Link D G) where

  A : Gr G 1 →* Module.End ℚ_[p] (Up L)
  A_snd : ∀ k k' : Gr G 1, k.2 = k'.2 → A k = A k'
  A_rat : ∀ (y : G.Cˣ × ℚˣ) (u : Up L),
    ((A (inclG G 1 (locC G y)) u : Up L) : VP D) = (L.rep (y.1 : G.C)).baseChange ℚ_[p] u
  A_O : ∀ (k : Gr G 1) (c : D.O) (u u' : Up L), (u' : VP D) = (actQ D c).baseChange ℚ_[p] u →
    ((A k u' : Up L) : VP D) = (actQ D c).baseChange ℚ_[p] (A k u)

  abelian₂ : AddSubgroup (Up L)
  isLat : IsULat L abelian₂
  stab : ∀ k : Gr G 1, abelian₂.map (A k).toAddMonoidHom = abelian₂ ↔ ∀ w, k.2 w ∈ Kres p (G.Fw w) G.n 1
  trans : ∀ Λ, IsULat L Λ → ∃ k : Gr G 1, abelian₂.map (A k).toAddMonoidHom = Λ

def latAf (S : Set (VQ D)) : AddSubgroup (AfP p ⊗[ℚ] VQ D) :=
  AddSubgroup.closure {w | ∃ (c : AfP p), ∃ u ∈ S, IsIntAf c ∧ w = c ⊗ₜ u}

def lattice₂ (S : Set (VQ D)) : AddSubgroup (VP D) :=
  AddSubgroup.closure {w | ∃ (c : ℤ_[p]), ∃ u ∈ S, w = (c : ℚ_[p]) ⊗ₜ u}

def actAf (L : Link D G) (g : (AfP p ⊗[ℚ] G.C)ˣ) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  actOn L.rep (AfP p) (g : AfP p ⊗[ℚ] G.C)

structure RealData {N : ℕ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} (L : Link D G) (A : PAct L)
    (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (X : MP D N ρ) (a : Dat G v β) where

  j : X.Dl.La →+ VQ D
  j_inj : Function.Injective j
  j_span : Submodule.span ℚ (Set.range j) = ⊤
  j_lin : ∀ (c : D.O) z, j (c • z) = actQ D c (j z)

  c₀ : ℚ
  c₀_pos : 0 < c₀
  form : ∀ z z', c₀ * (X.Dl.EF z z' : ℚ) = 2 * D.EF.baseChange ℚ (L.rep (β⁻¹ : G.Cˣ) (j z)) (j z')
  lat : latAf (Set.range j) = (LaHat D).map (actAf L (x⁻¹ * a.1.1.1.1)).toAddMonoidHom
  mark : ∀ l : D.La, ∃ w ∈ latAf (Set.range j),
    actAf L (x⁻¹ * a.1.1.1.1) (inAf D l) = (1 : AfP p) ⊗ₜ j (X.t l) + N • w
  mult : ∃ u : (AfP p)ˣ, IsIntAf (u : AfP p) ∧ IsIntAf ((u⁻¹ : (AfP p)ˣ) : AfP p) ∧
    ((uSimR (AfP p) a.1.1 : (AfP p)ˣ) : AfP p) = algebraMap ℚ (AfP p) c₀ * u * t
  latp : (lattice₂ (Set.range j)).comap (Up L).subtype.toAddMonoidHom = A.abelian₂.map (A.A a.1.2).toAddMonoidHom
  multp : ‖(((a.1.2.1 : GL (Fin 1) (Qr p 1)).val 0 0 : Qr p 1) : PadicAlgCl p)‖ = ‖((c₀ : ℚ) : ℚ_[p])‖

  Pq : VQ D →ₗ[ℚ] (Fin D.g → ℂ)
  Pq_j : ∀ z, Pq (j z) = X.P z

  Jc : ℝ ⊗[ℚ] G.C
  J_eq : ∀ u : ℝ ⊗[ℚ] VQ D, LinearMap.liftBaseChange ℝ Pq (actOn L.rep ℝ Jc u) =
    Complex.I • LinearMap.liftBaseChange ℝ Pq u
  line : G.psiR v Jc *ᵥ a.2.1 = (if v.embedding (L.e D.ω) = D.ρc then Complex.I else -Complex.I) • a.2.1

def Realizes {N : ℕ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} (L : Link D G) (A : PAct L)
    (v : InfinitePlace G.F) (P : Form G) (X : MP D N ρ) (a : Dat G v P.β) : Prop :=
  Nonempty (RealData L A v P.β P.trivAf.choose P.trivAf.choose_spec.choose X a)

abbrev FSame (L : Link D G) (N : ℕ) (v : InfinitePlace G.F) (P : Form G) (a b : Dat G v P.β) : Prop :=
  Same G v P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec (L.KN N) (KpOne G) a b

end UpperTheory.ComplexUniformization
