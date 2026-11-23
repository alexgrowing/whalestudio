import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordAdditive

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedAdd

open GlobalTheory.FormalPoint GlobalTheory.TorusCoord ReciprocityTheory.ChartRestriction.G.DVR

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

theorem red_iff_over (x : T ⟶ G) (g : GtPt D T) :
    U.Red x g ↔ ∀ (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (r : (Over.map (thick R I e)).obj Z ⟶ T) (a : Z ⟶ thickObj R I e G),
      (Over.map (thick R I e)).map a ≫ fstG I e G = r ≫ x → im (U.gt e) a = r ≫ g.b ∧
        ∀ χ z J, Good D.P.L z J →
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J = val (g.s χ) r.left z J := by
  constructor
  · intro h e Z r a ha
    obtain ⟨h₁, h₂⟩ := h e _ r.left ((Over.map (thick R I e)).map a).left (congrArg (fun q => q.left) ha)
    exact ⟨Over.OverMorphism.ext h₁, h₂⟩
  · intro h e Z r y hy
    have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨h₁, h₂⟩ := h e (Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk r w) (Over.homMk y rfl)
      (Over.OverMorphism.ext hy)
    exact ⟨congrArg (fun q => q.left) h₁, h₂⟩

theorem map_one_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
  have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem red_one {g : GtPt D T} (h : g.IsZero) : U.Red 1 g := by
  rw [red_iff_over]
  intro e Z r a ha
  obtain rfl : a = 1 := eq_of_map_fstG (by rw [ha, map_one_fstG, MonObj.comp_one])
  refine ⟨by rw [im_one, h.1]; exact (MonObj.comp_one r).symm, fun χ z J hJ => ?_⟩
  have t₁ := val_unit (U.gt e) χ (Z := Z) (z := z) hJ
  exact t₁.trans ((val_corr hJ (h.2 χ) r.left).trans (val_one _)).symm

variable {U} in

theorem red_mul (hG : GlobalFnsSt) {g g' g'' : GtPt D T} {x x' : T ⟶ G} (hx : U.Red x g)
    (hx' : U.Red x' g') (h : g.IsAdd g' g'') : U.Red (x * x') g'' := by
  rw [red_iff_over] at hx hx' ⊢
  intro e Z r y hy
  obtain ⟨a, ha⟩ := exists_lift_fstG (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x')
  obtain rfl : y = a * b := eq_of_map_fstG (by rw [hy, map_mul_fstG, ha, hb, MonObj.comp_mul])
  obtain ⟨a₁, a₂⟩ := hx e Z r a ha
  obtain ⟨b₁, b₂⟩ := hx' e Z r b hb
  refine ⟨by rw [im_mul, a₁, b₁, h.1]; exact (MonObj.comp_mul _ _ _).symm, fun χ z J hJ => ?_⟩
  have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a * b)).left z J *
      th D z J (cP D _ χ) (im (U.gt e) a) (im (U.gt e) b) =
      val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J *
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map b).left z J :=
    val_t_mul_points (U.gt e) hG χ a b z J hJ
  have e₂ : val (g''.s χ) r.left z J * th D z J (r ≫ cP D T χ) (r ≫ g.b) (r ≫ g'.b) =
      val (g.s χ) r.left z J * val (g'.s χ) r.left z J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub r hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) r.left).trans (val_mul hJ _ _ _))
  rw [a₁, b₁, a₂ χ z J hJ, b₂ χ z J hJ] at e₁
  rw [comp_cP] at e₂
  exact mul_right_cancel (e₁.trans e₂.symm)

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : PreU I D A G}

variable (I φ) in

abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (levelMap I φ e)

variable (I φ) in

def levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I φ e) ⟶ Over.mk (spMap φ) :=
  Over.homMk (thick S (I.map φ) e) (levelMap_thick I φ e).symm

variable [IsLocalRing S] [IsHausdorff (I.map φ) S]

omit [IsDomain R] in

theorem pt_ext {B : Over (Spec (CommRingCat.of R))} {b b' : Over.mk (spMap φ) ⟶ B}
    (h : ∀ e, levι I φ e ≫ b = levι I φ e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e => congrArg (·.left) (h e))

variable [IsNoetherianRing S]

theorem isAdd_of_red (hG : GlobalFnsSt) {x x' : Over.mk (spMap φ) ⟶ G} {g g' g'' : GtPt D (Over.mk (spMap φ))}
    (h : U.Red x g) (h' : U.Red x' g') (h'' : U.Red (x * x') g'') : GtPt.IsAdd g g' g'' := by
  rw [red_iff_over] at h h' h''
  choose a ha using fun e => exists_lift_fstG (levι I φ e ≫ x)
  choose a' ha' using fun e => exists_lift_fstG (levι I φ e ≫ x')
  have k := fun e => h e _ _ _ (ha e)
  have k' := fun e => h' e _ _ _ (ha' e)
  have k'' := fun e => h'' e _ (levι I φ e) (a e * a' e) (by rw [map_mul_fstG, ha, ha', MonObj.comp_mul])
  have hb : g''.b = g.b * g'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (k e).1, ← (k' e).1, ← (k'' e).1, im_mul]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.isGen χ) (g'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g''.b χ h) (prod_cub (DegPre.cT D _ χ) g.b g'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g.b χ h) (CoordAdd.prod_gtφT g'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e * a' e)).left z J *
        th D (T := (Over.map (thick R I e)).obj (lev I φ e)) z J (cP D _ χ) (im (U.gt e) (a e)) (im (U.gt e) (a' e)) =
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e)).left z J *
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a' e)).left z J :=
      val_t_mul_points (U.gt e) hG χ (a e) (a' e) z J hJ
    rw [(k e).1, (k' e).1, (k e).2 χ z J hJ, (k' e).2 χ z J hJ, (k'' e).2 χ z J hJ,
      ← comp_cP D (levι I φ e)] at e₁
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I φ e) hJ _ _ _))).trans
      (e₁.trans (val_mul hJ _ _ _).symm)

theorem isZero_of_red {g : GtPt D (Over.mk (spMap φ))} (h : U.Red 1 g) : g.IsZero := by
  rw [red_iff_over] at h
  have k := fun e => h e _ (levι I φ e) 1 (by rw [map_one_fstG, MonObj.comp_one])
  have hb : g.b = 1 := pt_ext (I := I) fun e => by rw [MonObj.comp_one, ← (k e).1, im_one]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (g.isGen χ) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (CoordAdd.prod_gtφT g.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · exact ((k e).2 χ z J hJ).symm.trans
      ((val_unit (U.gt e) χ (Z := lev I φ e) (z := z) hJ).trans (val_one _).symm)

end Complete

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (x x' x'' : TA V W ⟶ G) (g g' g'' : GtPt D (TA V W)), U.Red x g → U.Red x' g' → U.Red x'' g'' → (x'' = x * x' ↔ GtPt.IsAdd g g' g'') ∧ (x = 1 ↔ g.IsZero)) := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW x x' x'' g g' g'' h h' h''
  have := hV.1
  have := hW.1
  have := hW.2.2.2.2
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩⟩
  · exact isAdd_of_red (φ := algebraMap V W) hG h h' (e ▸ h'')
  · exact RedOnto.red_unique (φ := algebraMap V W) h'' (red_mul hG h h' e)
  · exact isZero_of_red (φ := algebraMap V W) (e ▸ h)
  · exact RedOnto.red_unique (φ := algebraMap V W) h (red_one U e)

end GlobalTheory.UU.RedAdd

end
