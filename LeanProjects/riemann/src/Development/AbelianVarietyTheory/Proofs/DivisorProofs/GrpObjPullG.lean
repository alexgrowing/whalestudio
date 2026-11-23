import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut LevelMod)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev pullG (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) : Over X' :=
  (Over.pullback (φ ≫ (barComp TF.Y Z).ι)).obj TF.Y.t.G

abbrev pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    (pullG TF Z φ).left ⟶ TF.Y.t.G.left :=
  pullback.fst _ _

abbrev pullAct (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    OAct (𝓞 E) (pullG TF Z φ) :=
  OAct.pullback (φ ≫ (barComp TF.Y Z).ι) TF.Y.t.G TF.Y.t.act

instance grpObj_pullG (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    GrpObj (pullG TF Z φ) :=
  inferInstance

theorem isGrpPullback_pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    IsGrpPullback (pullG TF Z φ) TF.Y.t.G (φ ≫ (barComp TF.Y Z).ι) (pullψ TF Z φ) :=
  isGrpPullback_pullback _ _

theorem pullAct_pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (a : 𝓞 E) :
    ((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ = pullψ TF Z φ ≫ (TF.Y.t.act.act a).left :=
  pullback.lift_fst _ _ _

variable {Γ : Type} [Group Γ]

def IsEqvAct {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X') [GrpObj G'] (act' : OAct (𝓞 E) G')
    (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  (∀ γ, IsGrpPullback G' G' (ρ' γ).hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    ∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁

def MovesEta (TF : TorFlag Xo c) (Z : Comp Xo c) (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z))
    {X' : Scheme.{0}} (ℓ : V₀ TF.Y Z ⟶ X') (G' : Over X') (ψ : G'.left ⟶ TF.Y.t.G.left)
    (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  ∀ (γ : Γ) (a b : Dw.La), (Submodule.Quotient.mk b : LevelMod Dw l) = (ι γ)⁻¹ (Submodule.Quotient.mk a) →
    ∀ w w' : V₀ TF.Y Z ⟶ G'.left, w ≫ G'.hom = ℓ → w' ≫ G'.hom = ℓ →
      w ≫ ψ = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ →
      w' ≫ ψ = i₀ TF.Y Z ≫ (TF.Y.oF.eta a).left ≫ TF.Y.m.φ →
      w ≫ m γ = (ρ γ).hom ≫ w'

def IsTorsI (I : Ideal (𝓞 E)) {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] (act' : OAct (𝓞 E) G') {T : Over X'}
    (P : T ⟶ G') : Prop :=
  ∀ a ∈ I, P ≫ act'.act a = 1

def TorsLevel (I : Ideal (𝓞 E)) (ι : Γ →* LevelAut Dw l) {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X')
    [GrpObj G'] (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X'), ∃ e : (Over.mk t ⟶ G') → LevelMod Dw l,
    (∀ P Q, IsTorsI I act' P → IsTorsI I act' Q → e (P * Q) = e P + e Q) ∧
    (∀ P (a : 𝓞 E), IsTorsI I act' P → e (P ≫ act'.act a) = a • e P) ∧
    (∀ P Q, IsTorsI I act' P → IsTorsI I act' Q → e P = e Q → P = Q) ∧
    ∀ γ, t ≫ (ρ' γ).hom = t → ∀ P Q : Over.mk t ⟶ G', IsTorsI I act' P → Q.left = P.left ≫ m γ →
      e Q = ι γ (e P)

end GlobalTheory.EqvAct
