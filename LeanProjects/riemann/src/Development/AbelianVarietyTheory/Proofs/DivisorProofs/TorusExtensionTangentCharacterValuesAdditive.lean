import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtTanClass

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_unit {T : Over (Sp R)} (g : GtPt D T) (hb : g.b = 1) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ T.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (g.s χ) q z J = Geo.Tor.gm q z ⊤ ρ := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T g.b χ) (ε' := DegPre.gtε)
    (fun U _ h => Eq.symm (by
      refine (prod_pt g.b χ h).trans ?_
      rw [hb, _root_.mul_one]; simp)) (LB.oneGen D.P.L (Y := T.left))
    (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl (g.s χ) u (g.isGen χ) hu
  exact ⟨ρ, fun Z q z J hJ => by rw [hρ Z q z J hJ, vu Z q z J hJ, val_one, _root_.mul_one]⟩

omit [IsDomain R] in
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = toStkA z (f a) := by
  rw [gs_eq _ _ ⊤ trivial]
  have e := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom e.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ _ D gm ⟨o, ho, hp⟩ hb
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hb1 : gm.b = 1 := hb
  choose ρ hρ using exists_unit gm hb1
  choose u hu using fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).commRingCatIsoToRingEquiv.symm.surjective (ρ χ).val
  have hv : ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → (val (gm.s χ) q z J).val =
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (u χ)) := fun χ Z q z J hJ =>
    (congrArg Units.val (hρ χ Z q z J hJ)).trans ((gs_unit q z ⊤ trivial _).symm.trans
      (congrArg (gs q z ⊤) (hu χ).symm))
  have h1 : ∀ χ, TrivSqZeroExt.fst (u χ : DualNumber R) = 1 := fun χ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt R)
    have e : val (gm.s χ) (redE R) (cpt R) J = 1 := by
      have e₁ := (val_corr hJ (hp.2 χ) (𝟙 (Sp R))).trans (val_pull hJ _ _ _)
      have e₂ := (val_corr hJ (ho.2 χ) (𝟙 (Sp R))).trans (val_one _)
      rw [← e₂, e₁]
      congr 1
    have e' := hv χ _ (redE R) (cpt R) J hJ
    rw [e] at e'
    refine toStkA_injective (A := R) ?_
    rw [map_one]
    exact (gs_spMap (TrivSqZeroExt.fstHom R R R).toRingHom (cpt R) (u χ)).symm.trans e'.symm
  have hm : ∀ χ χ', (u (χ + χ') : DualNumber R) = u χ * u χ' := fun χ χ' => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))
    have C : IsCub (th D (T := epsR R) (cpt (DualNumber R)) J) := isCub_cubV D.cub hJ
    have e := cv_add gm hJ χ χ'
    rw [hb1, C.face₃, _root_.mul_one] at e
    have k : ∀ χ, (cv gm χ (cpt (DualNumber R)) J).val = toStkA (cpt (DualNumber R)) (u χ) := fun χ =>
      (hv χ _ (𝟙 _) _ J hJ).trans (gs_eq _ _ ⊤ trivial _)
    refine toStkA_injective (A := DualNumber R) ?_
    rw [map_mul]
    exact (k _).symm.trans ((congrArg Units.val e).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (k _) (k _))))
  refine ⟨AddMonoidHom.mk' (fun χ => TrivSqZeroExt.snd (u χ : DualNumber R)) fun χ χ' => ?_, fun χ Z q z J hJ => ?_⟩
  · rw [hm, DualNumber.snd_mul, h1, h1]; ring
  · refine (hv χ Z q z J hJ).trans (congrArg (fun x => gs q z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom x)) ?_)
    exact TrivSqZeroExt.ext (by simp [h1]) (by simp)

end GlobalTheory.MBLow.GtTanClass

end
