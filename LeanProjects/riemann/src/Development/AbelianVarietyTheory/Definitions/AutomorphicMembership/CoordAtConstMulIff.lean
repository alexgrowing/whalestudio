import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.ShFam.Descent GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Frame

variable (Z : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (P : FrPt Xo c R)

def frameOf : EigFrame Z (algebraMap c.F R) (GlobalTheory.AllWt.ptF P ≫ Z.j) := (exists_tie_frame P rfl).choose

theorem tie_frameOf : Comparison₂ P (frameOf Z P) := (exists_tie_frame P rfl).choose_spec

variable {Z P}

end Frame

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem IsCoord.const_mul {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
    {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k} (h : IsCoord Y p g n σ a) (b : c.F) :
    IsCoord Y p g n (constF e Y.Y b * σ) (φ b * a) := by
  obtain ⟨y, ψ, φ₁, f, t, t', r, h1, h2, h3, h4, h5⟩ := h
  refine ⟨y, ψ, φ₁, f, t, t', φ₁ b * r, h1, h2, h3, ?_, ?_⟩
  · rw [map_mul, h4, mul_assoc]
    exact congrArg (· * _) (RingHom.congr_fun h2.2.1 b).symm
  · rw [map_mul, h5, mul_assoc, h3.2.1]
    rfl

theorem IsCoord.carries {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
    {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k} (h : IsCoord Y p g n σ a) : Y.Carries p g := by
  obtain ⟨y, ψ, φ₁, f, t, t', -, h1, h2, h3, -⟩ := h
  exact ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩

def CoordAt {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ IsCoord Y p (frameOf Z P) n σ a

def Carried {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ Y.Carries p (frameOf Z P)

def CarriedC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) : Prop := letI := ι.toAlgebra; Carried (k := ℂ) Y P

def CoordAtC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : ℂ) : Prop :=
  letI := ι.toAlgebra; CoordAt (k := ℂ) Y P n σ a

variable {Y}

theorem CoordAt.const_mul {k : Type} [Field k] [Algebra c.F k] {P : FrPt Xo c k} {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k}
    (h : CoordAt Y P n σ a) (b : c.F) : CoordAt Y P n (constF e Y.Y b * σ) (algebraMap c.F k b * a) :=
  h.imp fun _ hp => ⟨hp.1, hp.2.const_mul Y b⟩

theorem coordAt_const_mul_iff {k : Type} [Field k] [Algebra c.F k] {P : FrPt Xo c k} {n : Letter Dw → ℤ} {σ : Y.Y.Fn}
    {a : k} {b : c.F} (hb : b ≠ 0) :
    CoordAt Y P n (constF e Y.Y b * σ) a ↔ CoordAt Y P n σ (algebraMap c.F k b⁻¹ * a) := by
  constructor
  · intro h
    have := h.const_mul b⁻¹
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hb, map_one, one_mul] at this
  · intro h
    have := h.const_mul b
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hb, map_one, one_mul] at this

theorem CoordAt.carried {k : Type} [Field k] [Algebra c.F k] {P : FrPt Xo c k} {n : Letter Dw → ℤ} {σ : Y.Y.Fn} {a : k}
    (h : CoordAt Y P n σ a) : Carried Y P := h.imp fun _ hp => ⟨hp.1, hp.2.carries Y⟩

variable {r : ℕ}

end Free

end GlobalTheory.ShFam.Pad
