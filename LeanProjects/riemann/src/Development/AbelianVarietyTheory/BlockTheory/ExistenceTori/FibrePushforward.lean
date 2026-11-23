import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeStabSet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsSplitOff (l : Level H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M'

variable {Xo : Moduli Dw l}

section Fibre

variable {Ω : Type} [CommRing Ω]

def toFib (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : T ⟶ Gx x :=
  (lift (Over.homMk t rfl : Over.mk (t ≫ x) ⟶ Over.mk x) a).left

def push {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') {T : Scheme.{0}} (t : T ⟶ Sp Ω)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : T ⟶ Xo.univ.t.G.left :=
  toFib x t a ≫ ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left

def Sends {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Prop :=
  (lift (𝟙 (Over.mk x)) a).left ≫ ψ = (lift (𝟙 (Over.mk x')) b).left

def IsLinHom {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x') : Prop :=
  ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ∧
  (∀ (T : Scheme.{0}) (t : T ⟶ Sp Ω) (a₁ a₂ : Over.mk (t ≫ x) ⟶ Xo.univ.t.G)
      (b₁ b₂ : Over.mk (t ≫ x') ⟶ Xo.univ.t.G),
    b₁.left = push ψ t a₁ → b₂.left = push ψ t a₂ → (b₁ * b₂).left = push ψ t (a₁ * a₂)) ∧
  ∀ r : 𝓞 E, (Over.mk x ◁ Xo.univ.t.act.act r).left ≫ ψ = ψ ≫ (Over.mk x' ◁ Xo.univ.t.act.act r).left

def IsLieImg (p : ℕ) {x x' : Sp Ω ⟶ Xo.X} (ψ : Gx x ⟶ Gx x')
    (v w : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) : Prop :=
  IsTanAt x v ∧ IsTanAt x' w ∧
    ∃ a : tEps x ⟶ Xo.univ.t.G, a.left = v ∧
      spMap (epsMul (p : Ω)) ≫ w = push ψ (spMap (algebraMap Ω (DualNumber Ω))) a

def IsThGen (x : Sp Ω ⟶ Xo.X) (s : LB.Sec (PPx x)) : Prop :=
  ∀ s' : LB.Sec (PPx x), ∃! a : Ω, ∀ i, s'.f i = scal x a i * s.f i

end Fibre

def IsHeckeIsog (p : ℕ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X}
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : Gx x ⟶ Gx x') : Prop :=
  x' ≫ Xo.s = x ≫ Xo.s ∧ IsLinHom ψ ∧
  (∀ b, ∃ a, Sends ψ a b) ∧
  (∀ a, Sends ψ a 1 ↔ a ∈ C) ∧
  (∀ (n : ℕ) (a₁ a₂ : Over.mk x ⟶ Xo.univ.t.G) (b₁ b₂ : Over.mk x' ⟶ Xo.univ.t.G) (e : Ωˣ), n.Coprime p →
    Sends ψ a₁ b₁ → Sends ψ a₂ b₂ →
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a₁ a₂ (unitOn e) →
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n b₁ b₂ (unitOn (e ^ (p ^ 2)))) ∧
  (∀ a : Dw.La, Sends ψ (toUnit _ ≫ Xo.univ.eta a) (toUnit _ ≫ Xo.univ.eta (p • a))) ∧
  (∀ a : Dw.La, Sends ψ (toUnit _ ≫ Xo.univ.etaA a) (toUnit _ ≫ Xo.univ.etaA (p • a)))

variable (Xo) (c : Coeff l)

abbrev Transport : Type 1 :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (x x' : Sp Ω ⟶ Xo.X),
    (Gx x ⟶ Gx x') → LB.Sec (PPx x) → LB.Sec (PPx x') → Prop

variable {𝔓 : Ideal (𝓞 E)} {p : ℕ}

def HeckeIdx (_h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) : Type :=
  {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y.x) Dw 𝔓 p i C}

def IsHeckePt (tr : Transport Xo c) (h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : HeckeIdx Xo c h i Ω y) (z : FrPt Xo c Ω) : Prop :=
  ∃ ψ : Gx y.x ⟶ Gx z.x, IsHeckeIsog p C.1 ψ ∧ (∀ τ j, IsLieImg p ψ (y.u τ j) (z.u τ j)) ∧
    tr Ω y.x z.x ψ y.s z.s

def TrTotal (tr : Transport Xo c) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (x x' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : Gx x ⟶ Gx x') (s : LB.Sec (PPx x)),
    x ≫ Xo.s = sOf c Ω → Xo.univ.t.HeckeKer (Over.mk x) Dw 𝔓 p i C → IsHeckeIsog p C ψ → IsThGen x s →
    ∃ s', IsThGen x' s' ∧ tr Ω x x' ψ s s'

def TrUnique (tr : Transport Xo c) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (x x' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)) (ψ : Gx x ⟶ Gx x') (s : LB.Sec (PPx x)) (s' s'' : LB.Sec (PPx x')),
    x ≫ Xo.s = sOf c Ω → Xo.univ.t.HeckeKer (Over.mk x) Dw 𝔓 p i C → IsHeckeIsog p C ψ → IsThGen x s →
    IsThGen x' s' → IsThGen x' s'' → tr Ω x x' ψ s s' → tr Ω x x' ψ s s'' → s' = s''

def FinSt : Prop :=
  ∀ (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h : IsSplitOff l 𝔓 p) (i : ℕ),
    HkFin (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => HeckeIdx Xo c h i Ω y)

def TotalSt : Prop :=
  ToroidalHeckeCompatibility (D := Dw) → ∀ (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h : IsSplitOff l 𝔓 p) (i : ℕ) (tr : Transport Xo c),
    TrTotal Xo c tr 𝔓 p i →
    HkTotal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => HeckeIdx Xo c h i Ω y)
      (fun Ω _ _ _ y C z => IsHeckePt Xo c tr h i Ω y C z)

def FunSt : Prop :=
  ToroidalHeckeCompatibility (D := Dw) → ∀ (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h : IsSplitOff l 𝔓 p) (i : ℕ) (tr : Transport Xo c),
    TrUnique Xo c tr 𝔓 p i →
    HkFun (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => HeckeIdx Xo c h i Ω y) (fun Ω _ _ _ y C z => IsHeckePt Xo c tr h i Ω y C z)

example {Ω : Type} [CommRing Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) : IsThGen y.x y.s := y.gen

example {Ω : Type} [CommRing Ω] (x : Sp Ω ⟶ Xo.X) (a : Over.mk x ⟶ Xo.univ.t.G) : Sends (𝟙 (Gx x)) a a := by
  simp [Sends]

example {Ω : Type} [CommRing Ω] (x : Sp Ω ⟶ Xo.X) : IsLinHom (𝟙 (Gx x)) := by
  have hp : ∀ (T : Scheme.{0}) (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G), push (𝟙 (Gx x)) t a = a.left := by
    intro T t a
    unfold push toFib
    rw [Category.id_comp, ← Over.comp_left, lift_snd]
  refine ⟨Category.id_comp _, fun T t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => by simp⟩
  rw [hp] at h₁ h₂ ⊢
  rw [Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂]

end GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
