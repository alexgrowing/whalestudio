import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CoordAdd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem corr_of_thick {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z J, Good L z J → val u (thick R I e) z J = val u' (thick R I e) z J) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := by
    refine Units.ext (AbelianPartIso.fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := ha _ (thick R I e) z J hJ
    rw [hv e z J hJ] at this
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, map_one, mul_eq_right.1 this.symm]
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable (I) in

abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (𝟙 _)

variable (I) in

abbrev levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I e) ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _

omit [IsDomain R] in
theorem levι_left (e : ℕ) : (levι I e).left = thick R I e :=
  (Category.comp_id _).symm.trans ((Over.w (levι I e)).trans (Category.id_comp _))

omit [IsDomain R] in
theorem toUnit_left (e : ℕ) : (toUnit (Over.mk (thick R I e))).left = thick R I e :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (thick R I e))))

def Lifts {e : ℕ} (g : GtCoord I D e G) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (a : lev I e ⟶ thickObj R I e G) : Prop :=
  pushHom (isGrpPullback_pullback G (thick R I e)) (lev I e) a = levι I e ≫ x ∧ im g a = levι I e ≫ gp.b ∧
    ∀ χ z J, Good D.P.L z J → val (g.t χ) a.left z J = val (gp.s χ) (levι I e).left z J

theorem exists_lifts {e : ℕ} (g : GtCoord I D e G) {x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G}
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G),
      xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ g.pG = toUnit _ ≫ gp.b ∧
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) xe.left)
        (LB.pullGen D.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) :
    ∃ a, Lifts g x gp a := by
  obtain ⟨xe, h₁, h₂, h₃⟩ := h
  have hw : xe.left ≫ (thickObj R I e G).hom = 𝟙 _ := by
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact (Over.w xe).trans (Category.id_comp _).symm
  have hu : (toUnit (Over.mk (thick R I e))).left = (levι I e).left := (toUnit_left e).trans (levι_left e).symm
  refine ⟨Over.homMk xe.left hw, Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_, fun χ z J hJ => ?_⟩
  · exact (congrArg (·.left) h₁).trans (congrArg (· ≫ x.left) hu)
  · exact (congrArg (·.left) h₂).trans (congrArg (· ≫ gp.b.left) hu)
  · have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ χ) (𝟙 _)).trans (val_pull hJ _ _ _))
    rw [Category.id_comp, Category.id_comp, hu] at this
    exact this

omit [IsDomain R] [IsCommMonObj G] in
theorem push_injective {e : ℕ} {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    Function.Injective (pushHom (isGrpPullback_pullback G (thick R I e)) T) := fun a b h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (·.left) h) ((Over.w a).trans (Over.w b).symm))

omit [IsDomain R] in

theorem pt_ext [IsLocalRing R] [IsHausdorff I R] {B : Over (Spec (CommRingCat.of R))}
    {b b' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B} (h : ∀ e, levι I e ≫ b = levι I e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e =>
    (congrArg (· ≫ b.left) (levι_left e)).symm.trans
      ((congrArg (·.left) (h e)).trans (congrArg (· ≫ b'.left) (levι_left e))))

theorem prod_gtφT {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (DegPre.cT D T χ * b).left)⁻¹ * h (DegPre.cT D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) = _
  rw [zpow_neg_one, zpow_neg_one, zpow_one, zpow_one]
  rfl

variable [IsLocalRing R] [IsNoetherianRing R] [IsHausdorff I R]

theorem isAdd_of_lifts (hGF : GlobalFnsSt) (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} {gp gp' gp'' : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) x gp a) (h' : ∀ e, ∃ a, Lifts (g e) x' gp' a)
    (h'' : ∀ e, ∃ a, Lifts (g e) (x * x') gp'' a) : GtPt.IsAdd gp gp' gp'' := by
  choose a ha using h
  choose a' ha' using h'
  choose a'' ha'' using h''
  have hm : ∀ e, a'' e = a e * a' e := fun e => push_injective (by
    rw [map_mul, (ha e).1, (ha' e).1, (ha'' e).1]
    exact MonObj.comp_mul _ _ _)
  have hb : gp''.b = gp.b * gp'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (ha e).2.1, ← (ha' e).2.1, ← (ha'' e).2.1, hm, im_mul]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp.isGen χ) (gp'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (prod_gtφT gp''.b χ h) (prod_cub (DegPre.cT D _ χ) gp.b gp'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (prod_gtφT gp.b χ h) (prod_gtφT gp'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have k := val_t_mul_points (g e) hGF χ (a e) (a' e) z J hJ
    have c : cubeVal (g e) χ z J (a e) (a' e) =
        cubV D.cub z J (levι I e ≫ DegPre.cT D _ χ) (levι I e ≫ gp.b) (levι I e ≫ gp'.b) := by
      unfold cubeVal
      rw [(ha e).2.1, (ha' e).2.1, comp_toUnit_assoc]
    rw [← hm, (ha e).2.2 χ z J hJ, (ha' e).2.2 χ z J hJ, (ha'' e).2.2 χ z J hJ, c] at k
    have := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I e) hJ _ _ _))).trans
      (k.trans (val_mul hJ _ _ _).symm)
    rw [levι_left] at this
    exact this

theorem isZero_of_lifts (hI : I ≠ ⊤) (g : ∀ e, GtCoord I D e G)
    {gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    (h : ∀ e, ∃ a, Lifts (g e) 1 gp a) : gp.IsZero := by
  choose a ha using h
  have hm : ∀ e, a e = 1 := fun e => push_injective (by
    rw [map_one, (ha e).1]
    exact MonObj.comp_one _)
  have hb : gp.b = 1 := pt_ext (I := I) fun e => by
    rw [MonObj.comp_one, ← (ha e).2.1, hm, im_one]
  refine ⟨hb, fun χ => corr_of_thick hI D.P.isLB (fun U _ h => ?_) (gp.isGen χ)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (prod_gtφT gp.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · have k := (ha e).2.2 χ z J hJ
    rw [hm, val_unit (g e) χ hJ, levι_left] at k
    exact k.symm.trans (val_one _).symm

end GlobalTheory.CoordAdd

namespace GlobalTheory

open CoordAdd in

theorem gtCoord_additive : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), (∀ (x x' : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp gp' gp'' : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x' ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp'.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp'.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (x * x') ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp''.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp''.s χ) (toUnit (Over.mk (thick R I e))).left)) → GtPt.IsAdd gp gp' gp'') ∧ ∀ gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (1 : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.IsZero := by
  intro hGF R _ _ _ I hR hI D A G _ _ U
  obtain ⟨_, -, -, _⟩ := hR
  exact ⟨fun x x' gp gp' gp'' h h' h'' => isAdd_of_lifts hGF hI U.gt (fun e => exists_lifts _ (h e))
    (fun e => exists_lifts _ (h' e)) (fun e => exists_lifts _ (h'' e)),
    fun gp h => isZero_of_lifts hI U.gt fun e => exists_lifts _ (h e)⟩

end GlobalTheory
