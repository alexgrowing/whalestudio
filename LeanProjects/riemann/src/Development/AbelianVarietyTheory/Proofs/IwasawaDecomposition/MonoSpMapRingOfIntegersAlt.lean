import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col)

namespace GlobalTheory.ShFam.BdArc

instance mono_spMap_ringOfIntegers (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) :=
  have : IsPreimmersion (spMap (algebraMap (𝓞 K) K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 K))
  inferInstance

def imTop : Filter ℂ := Filter.comap Complex.im Filter.atTop

def IsHolPts {A : Type} [CommRing A] (ψ : ℂ → (A →+* ℂ)) (r : ℝ) : Prop :=
  0 < r ∧ ∀ a, DifferentiableOn ℂ (fun u => ψ u a) (Metric.ball 0 r)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {N : ℕ} (X : Data E N)

def IsOrbit (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) : Prop :=
  0 < M ∧ γ ∈ X.Γ ∧ DifferentiableOn ℂ x {w | T < w.im} ∧ (∀ w : ℂ, T < w.im → x w ∈ X.dom) ∧
    ∀ w : ℂ, T < w.im → ∃ b ∈ Bor X.Ψ N, (∀ τ i, b τ i i = 1) ∧ x (w + M) = rmul (lact γ (x w)) b

def SamePos (x x' : Frame X.Ψ N) : Prop :=
  ∀ τ : X.Ψ, Submodule.span ℂ (col (mat x τ) '' {a | (a : ℕ) < X.p0}) =
    Submodule.span ℂ (col (mat x' τ) '' {a | (a : ℕ) < X.p0})

end Frames

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

def IsArc (Z : Model Xo c β) (σ : c.F →+* ℂ) {A : Type} [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z)
    (ψ : ℂ → (A →+* ℂ)) (r : ℝ) : Prop :=
  IsHolPts ψ r ∧ x ≫ genStr Z = spMap φ ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp φ = σ

def IsBdArc (Z : Model Xo c β) (σ : c.F →+* ℂ) {A : Type} [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z)
    (ψ : ℂ → (A →+* ℂ)) (r : ℝ) : Prop :=
  IsArc Z σ φ x ψ r ∧ (∀ s, (spMap (ψ 0) ≫ x) s ∈ genBd Z) ∧
    ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z

def Matches {Z : Model Xo c β} {σ : c.F →+* ℂ} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ) (y : FrPt Xo c (CAt σ)) : Prop :=
  GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (show A →+* CAt σ from ψ) ≫ x ∧
    ∀ τ i, ∃ w : Sp (DualNumber (CAt σ)) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap (CAt σ) (DualNumber (CAt σ))) ≫ GlobalTheory.AllWt.ptF y ∧
        w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (show A →+* CAt σ from ψ)) ≫ fr.v τ i

def SameLie {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  y.x = y'.x ∧ ∀ τ i, y.u τ i = y'.u τ i

def IsLift {σ : c.F →+* ℂ} {N : ℕ} (U : Unf Xo c σ N) (k : U.Comp) (y : ℂ → FrPt Xo c (CAt σ)) (T : ℝ)
    (x : ℂ → Frame (U.X k).Ψ N) : Prop :=
  ∀ w : ℂ, T < w.im → ∃ h : x w ∈ (U.X k).dom, SameLie (U.un k ⟨x w, h⟩) (y (eTwoPi w))

end GlobalTheory.ShFam.BdArc
