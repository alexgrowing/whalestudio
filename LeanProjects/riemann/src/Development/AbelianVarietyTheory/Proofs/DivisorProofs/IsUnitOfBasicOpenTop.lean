import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_of_basicOpen_top {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

abbrev fnSp (A : Type) [CommRing A] : A →+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_comp_spMap {R₀ A : Type} [CommRing R₀] [CommRing A] (α : R₀ →+* A) {Z : Scheme.{0}}
    (s : Z ⟶ Sp A) (r : R₀) : (s ≫ spMap α).appTop.hom (fnSp R₀ r) = s.appTop.hom (fnSp A (α r)) := by
  have nat := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.appTop.hom nat.symm

def fnOn {R₀ : Type} [CommRing R₀] (W : (Sp R₀).Opens) : R₀ →+* Γ(W.toScheme, ⊤) :=
  W.ι.appTop.hom.comp (fnSp R₀)

theorem appTop_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) :
    t.appTop.hom (fnOn W r) = s.appTop.hom (fnSp A (α r)) := by
  have e : t.appTop.hom (fnOn W r) = (t ≫ W.ι).appTop.hom (fnSp R₀ r) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [e, h, appTop_comp_spMap]

theorem gm_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) (u : Γ(W.toScheme, ⊤)ˣ) (v : Aˣ)
    (hu : (u : Γ(W.toScheme, ⊤)) = fnOn W r) (hv : (v : A) = α r) (z : Z) :
    gm t z ⊤ u = gm s z ⊤ (unitOn v) := by
  rw [GlobalTheory.UU.gm_top t, GlobalTheory.UU.gm_top s]
  congr 1
  apply Units.ext
  show t.appTop.hom (u : Γ(W.toScheme, ⊤)) = s.appTop.hom (fnSp A (v : A))
  rw [hu, hv, appTop_fnOn W α t s h r]

theorem isUnit_fnOn {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) :
    IsUnit (fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) r) := by
  set W := (Sp R₀).basicOpen (fnSp R₀ f)
  have hf : IsUnit (fnOn W f) := isUnit_of_basicOpen_top _ (by
    have e := Scheme.preimage_basicOpen W.ι (fnSp R₀ f)
    rw [Scheme.Opens.ι_preimage_self] at e
    exact e.symm)
  exact isUnit_of_dvd_unit (map_dvd (fnOn W) hr |>.trans (by rw [map_pow])) (hf.pow N)

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ) (r : D₁.X → R₀)
    (hu : ∀ y, (u y : Γ(W'.toScheme, ⊤)) = fnOn W' (r y)) (hr : ∀ y, algebraMap R₀ (FractionRing R₀) (r y) = κ₀ y) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine gm_fnOn W' (algebraMap R₀ (FractionRing R₀)) _ _ ?_ (r y) _ _ (hu y) (hr y).symm z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.RescaleLift
