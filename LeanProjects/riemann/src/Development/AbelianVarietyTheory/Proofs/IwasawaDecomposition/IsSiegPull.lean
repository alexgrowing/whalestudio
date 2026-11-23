import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

namespace GlobalTheory.SiegLoc

def SiegData (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S)
    (d N : ℕ) : Prop :=
  IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
    (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
    IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
    1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
    1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

theorem siegAt_iff (g : ℕ) (φ : InvFun ℤ) (n : ℕ) :
    SiegAt g φ n ↔ ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S)
      (_ : IsOpenImmersion j) (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      SiegData g φ n F S s j G e BD d N := Iff.rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def IsSiegPull {g n : ℕ} {F : SFam g n (zetaAway n)} {S : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S)
    (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R]
    {ω : R →+* c.F} (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S) : Prop :=
  ∃ (μ : C.t.G.left ⟶ G.left) (y : Xo.XF c ⟶ F.X) (α : C.oF.t.G.left ⟶ F.univ.A.left)
    (α₂ : (G2 C.oF.t.G).left ⟶ (G2 F.univ.A).left),
    IsFinite π ∧ π ≫ s = C.s ≫ spMap κ ∧ IsGrpPullback C.t.G G π μ ∧
    y ≫ j = C.j ≫ π ∧ IsGrpPullback C.oF.t.G F.univ.A y α ∧ IsSquare α α₂ ∧
    LBIso (abelian₂ C.oF.t.G C.oF.t.PP.L) (F.univ.P.pull α₂) ∧ C.m.φ ≫ μ = α ≫ e

end GlobalTheory.SiegLoc
