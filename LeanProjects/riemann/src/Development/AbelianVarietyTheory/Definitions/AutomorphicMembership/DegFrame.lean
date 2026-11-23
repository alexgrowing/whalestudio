import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

abbrev Letter : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def letters : List (Letter Dw) :=
  (List.finRange (Fintype.card (E →+* ℂ))).flatMap fun a =>
    (List.finRange (Dw.mult ((Fintype.equivFin (E →+* ℂ)).symm a))).map fun i => ⟨_, i⟩

abbrev Sym (E : Type) [Field E] : Type := (ℕ → Bool) × Option ℝ × (((E →+* ℂ) × ℕ) ⊕ ℕ)

def letterOf : ((E →+* ℂ) × ℕ) ⊕ ℕ → Option (Letter Dw)
  | .inl (τ, k) => if h : k < Dw.mult τ then some ⟨τ, ⟨k, h⟩⟩ else none
  | .inr k => (letters Dw)[k]?

open Classical in

def expo (w : Sym E →₀ ℤ) (x : Letter Dw) : ℤ := w.sum fun a n => if letterOf Dw a.2.2 = some x then n else 0

open Classical in

def parOf (w : Sym E →₀ ℤ) : Option ℝ := if h : w.support.Nonempty then h.choose.2.1 else none

variable {Dw}

open Classical in

def lnStep {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool) :
    ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ
  | .inl (τ, k) => if h : k < Dw.mult τ then Real.log (grNorm t x (lat t p x b) (u τ) ⟨k, h⟩) -
      (if b ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) else 0
  | .inr k => if h : k < (letters Dw).length then
      Real.log (grNorm t x (lat t p x b) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩) else 0

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def divOf (n : Letter Dw → ℤ) : Y.Y.Dv := ∑ x, n x • Y.gr x.1 x.2

def resP (v : HeightOneSpectrum (𝓞 F)) : ℕ := ringChar (𝓞 F ⧸ v.asIdeal)

def ioOf (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) : AlgebraicClosure F →+* ℂ_[p] :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
  haveI : Nonempty (AlgebraicClosure F →+* ℂ_[p]) := ⟨(IsAlgClosed.lift : AlgebraicClosure F →ₐ[ℚ] ℂ_[p]).toRingHom⟩
  Classical.epsilon fun io => ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O

open Classical in

def lgOf (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (Y.gr_spec (below y.1)).choose_spec.choose
    let t := (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

abbrev Mets (C : CxSt F) : Type := ∀ (_ : Option ℝ) (σ : F →+* ℂ) (n : Letter Dw → ℤ), C.Met Y.Y σ (divOf Y n)

def adlOf {C : CxSt F} (hm : Mets Y C) (w : Sym E →₀ ℤ) : Adl C Y.Y where
  D := divOf Y (expo Dw w)
  n := 1
  m σ := hm (parOf w) σ _
  ci := 0
  lg := lgOf Y w

variable (Dw) in

def rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : Sym E →₀ ℤ :=
  if i < Dw.p then Finsupp.single (a, R, .inl (τ, i)) 1
  else Finsupp.single (a, R, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) (-1)

def wholeSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => Finsupp.single (a, R, .inr k) 1
  | .inr k => Finsupp.single (a, R, .inr (Fin.rev k)) (-1)

variable (Dw) in

def detSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) : Sym E →₀ ℤ :=
  ∑ i ∈ Finset.range (Dw.p + Dw.q), rootSym Dw a R τ i

def IsFlat (τ : E →+* ℂ) (σ : Y.Y.Fn) : Prop :=
  ∀ y : Y.Y.X, (divOf Y (expo Dw (detSym Dw (fun _ => false) none τ))).GeneratesAt y σ

def IsCoord {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x)
    (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ (y : Y.Y.X) (ψ : Y.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* Y.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt Y.Y y ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ) (r : Y.Y.X.presheaf.stalk y),
    p = spMap ψ ≫ stalkPt Y.Y y ∧ f.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t ∧
      f.Tri ψ g t' ∧
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField r =
        σ * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      a = ψ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k)

def FlagPt.frame {Ω : Type} [Field Ω] (y : FlagPt Z Ω) : EigFrame Z y.fK (y.y ≫ genι Z) :=
  ⟨y.u, y.tan, y.eig, y.basis⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (fl : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (fl.C k) C)

def arIn : ArIn D.what₂.Tau N (D.R.f * N) s.Comp where
  A _ := Sym D.host.E →₀ ℤ
  num k := polar fun w => (adlOf (fl.C k) (hm k) w).arTop
  root a R x _ := rootSym S.Dw a (some R) (DV.tauEmb D x.1) x.2
  whole a R x _ := wholeSym a (some R) x

def setB (κ : Lv A) (B : ℝ) : Finset ℕ :=
  (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (NumberField.discr D.host.E).natAbs * κ.l.M').primeFactors

def flatSec (k : s.Comp) (τ : D.what₂.Tau) : (fl.C k).Y.Fn := Classical.epsilon (IsFlat (fl.C k) (DV.tauEmb D τ))

def innerPt (k : s.Comp) : (fl.C k).Y.X :=
  Classical.epsilon fun x => IsClosed ({x} : Set (fl.C k).Y.X) ∧ (fl.C k).π x ∉ genBd s.T.Z

def flatSt : FlatSt s where
  sv τ y := Classical.epsilon fun a => ∃ (k : s.Comp) (p : Sp Qb ⟶ (fl.C k).Y.X), p ≫ (fl.C k).π = y.y ∧
    IsCoord (fl.C k) p y.frame (expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))) (flatSec s fl k τ) a
  ht B k τ := (adlOf (fl.C k) (hm k) (detSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFrame (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  (adlOf (fl.C k) (hm k) (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFlat (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  degFrame s fl hm k τ + (S.Dw.q : ℝ) * (Real.log A.H.d -
    Real.log (NumberField.discr D.host.E).natAbs / (Module.finrank ℚ D.host.E : ℝ))

end GlobalTheory.ShFam.Pad
