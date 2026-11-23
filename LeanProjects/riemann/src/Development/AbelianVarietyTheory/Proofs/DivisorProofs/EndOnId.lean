import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

section Two

variable {B : Scheme.{0}} (H : Over B) [GrpObj H]
  {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
  {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
  {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
  {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]

def Spread₂ (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    (ρ : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ψ : Sp W ⟶ B)
    (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (φW : GW.left ⟶ H.left)
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ GW)
    (Ω : Type) (_ : Field Ω) (α : W →+* Ω) (b₁ : V₁ →+* Ω) (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0)
    (GΩ : Over (Sp Ω)) (_ : GrpObj GΩ) (n : GΩ.left ⟶ GW.left) (hn : IsGrpPullback GΩ GW (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (κ : Type) (_ : Field κ) (c : W →+* κ) (b₂ : V₂ →+* κ) (hb₂ : ∀ x ∈ maximalIdeal V₂ ^ (0 + 1), b₂ x = 0)
    (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ GW.left) (hm : IsGrpPullback Gκ GW (spMap c) m)
    (m₂ : Gκ.left ⟶ G₂.left) (hm₂ : IsGrpPullback Gκ G₂ (spMap b₂) m₂),
    IsGrpPullback GW H ψ φW ∧ IsMonHom j ∧ Function.Injective α ∧ IsLocalHom c ∧
      spMap α ≫ ψ = spMap b₁ ≫ ξ₁ ∧ spMap c ≫ ψ = spMap b₂ ≫ ξ₂ ∧ n ≫ φW = n₁ ≫ β₁ ∧ m ≫ φW = m₂ ≫ β₂ ∧
      GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁ ∧
      GlobalTheory.TorusPart.pullTorus hm j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb₂ hm₂

def TorAt (U : Unif (maximalIdeal V₁) D₁ A₁ G₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (z : F)
    (c : D₁.toPre.X →+ ℤ) (x : TFK (R := V₁) F ⟶ A₁.A) : Prop :=
  ∃ (τ : Multiplicative D₁.toPre.X →* Fˣ) (q : QkPt D₁.toPre F k),
    (∀ χ, (τ (Multiplicative.ofAdd χ) : F) = z ^ c χ) ∧ q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU U.toUnifPre F k q x

end Two

section Model
open Classical

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)

def EndOn (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G) : Prop :=
  ((Over.pullback FinalForm.u₀).map f).left ≫ FinalForm.φ = FinalForm.φ ≫ Fm.left

def SecOn (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left) : Prop :=
  h ≫ FinalForm.G.hom = Wo.ι ∧
    ∀ (x : Sp Ω ⟶ Wo.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀), x ≫ Wo.ι = M.pt → x' ≫ FinalForm.φ ≫ FinalForm.G.hom = M.pt →
      x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ FinalForm.φ

def Link {T : Scheme.{0}} (x : T ⟶ M.Z) (u : T ⟶ Sp S.R) (A : Over T) [GrpObj A] (φ : A.left ⟶ ρ.P.A.left)
    (gm : A.left ⟶ FinalForm.G.left) : Prop :=
  IsGrpPullback A FinalForm.G x gm ∧
    (∀ (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ (T' : Scheme.{0}) (p p' : T' ⟶ A.left),
      p' ≫ A.hom = p ≫ A.hom → p' ≫ φ = p ≫ φ ≫ f.left → p' ≫ gm = p ≫ gm ≫ Fm.left) ∧
    ∀ (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left), SecOn FinalForm a Wo h →
      ∀ (T' : Scheme.{0}) (p : T' ⟶ A.left) (x' : T' ⟶ Wo.toScheme), x' ≫ Wo.ι = p ≫ A.hom ≫ x →
        p ≫ φ = p ≫ A.hom ≫ u ≫ (ρ.pt a).left → p ≫ gm = x' ≫ h

theorem Link.pull {T T₁ : Scheme.{0}} {x : T ⟶ M.Z} {u : T ⟶ Sp S.R} {A : Over T} [GrpObj A] {φ : A.left ⟶ ρ.P.A.left}
    {gm : A.left ⟶ FinalForm.G.left} (h : Link FinalForm x u A φ gm) {v : T₁ ⟶ T} {A' : Over T₁} [GrpObj A'] {w : A'.left ⟶ A.left}
    (hw : IsGrpPullback A' A v w) : Link FinalForm (v ≫ x) (v ≫ u) A' (w ≫ φ) (w ≫ gm) := by
  have e : w ≫ A.hom = A'.hom ≫ v := hw.1.w
  refine ⟨hw.comp h.1, fun f Fm hf T' p p' h₁ h₂ => ?_, fun a Wo s hs T' p x' h₁ h₂ => ?_⟩
  · have := h.2.1 f Fm hf T' (p ≫ w) (p' ≫ w) (by rw [Category.assoc, Category.assoc, e, reassoc_of% h₁])
      (by simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this
  · have := h.2.2 a Wo s hs T' (p ≫ w) x' (by rw [h₁, Category.assoc, reassoc_of% e])
      (by rw [Category.assoc, Category.assoc, reassoc_of% e]; simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this

end Model

end GlobalTheory.Poinc.Sep.Spz
