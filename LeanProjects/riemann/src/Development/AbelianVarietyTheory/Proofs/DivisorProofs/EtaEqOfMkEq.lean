import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

def ValAt {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (p : (torsion G n).left) (c : M) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V),
    y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ →
      y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion.ι G n).left = z ≫ w c

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSec_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    (i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) ≫ TF.Y.t.G.hom = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
  have h1 := TF.Y.m.cart.1.w
  have h2 := Over.w (TF.Y.oF.eta b)
  simp only [Category.assoc] at h1 ⊢
  rw [h1, ← Category.assoc ((TF.Y.oF.eta b).left), h2, reassoc_of% hℓ, j₀_ι]
  exact congrArg (i₀ TF.Y Z ≫ ·) (Category.id_comp _)

def etaSec (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  pullback.lift _ _ (etaSec_w TF Z φ ℓ hℓ b)

theorem eta_eq_of_mk_eq (TF : TorFlag Xo c) {b b' : Dw.La}
    (h : (Submodule.Quotient.mk b : LevelMod Dw l) = Submodule.Quotient.mk b') :
    TF.Y.oF.eta b = TF.Y.oF.eta b' := by
  rw [Submodule.Quotient.eq] at h
  have := TF.Y.oF.eta_add b' (b - b')
  rwa [add_sub_cancel, TF.Y.oF.eta_ker _ h, mul_one] at this

def etaSecL (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  Quot.liftOn x (etaSec TF Z φ ℓ hℓ) fun b b' h => by
    have e := eta_eq_of_mk_eq TF (b := b) (b' := b') (Quot.sound h)
    unfold etaSec
    congr 2
    rw [e]

theorem etaSecL_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) :
    etaSecL TF Z φ ℓ hℓ x ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = ℓ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact pullback.lift_snd _ _ _

theorem etaSecL_ψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk b) ≫ GlobalTheory.EqvAct.pullψ TF Z φ =
      i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ :=
  pullback.lift_fst _ _ _

end GlobalTheory.TorsSpec
