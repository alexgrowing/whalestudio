import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.TorMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def germScal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) :
    W →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)

theorem gs_scal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) (c : W) :
    gs (𝟙 Z) z ⊤ (scal (R := W) r c) = germScal r z c :=
  gs_eq (𝟙 Z) z ⊤ trivial _

def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  pushHom (isGrpPullback_pullback G (thick R I e)) T

theorem push_left (e : ℕ) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (y : T ⟶ thickObj R I e G) :
    (push I e G T y).left = y.left ≫ (fstG I e G).left := rfl

theorem push_inj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Injective (push I e G T) := fun y y' h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w y).trans (Over.w y').symm))

theorem push_surj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Surjective (push I e G T) := fun x =>
  ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

def Coord {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))
    (a : Multiplicative D.X →* Wˣ) (y : T ⟶ thickObj R I e G) : Prop :=
  GlobalTheory.TorusCoord.im g y = 1 ∧ ∀ (χ : D.X) (z : T.left) (J), Good D.P.L z J →
    val (g.t χ) y.left z J = Units.map (germScal r z : W →* _) (a (Multiplicative.ofAdd χ))

section
variable {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))

theorem coord_one : Coord g r 1 (1 : T ⟶ thickObj R I e G) :=
  ⟨GlobalTheory.TorusCoord.im_one g, fun χ z J hJ => (GlobalTheory.TorusCoord.val_unit g χ hJ).trans (map_one _).symm⟩

theorem val_mul_of (hG : GlobalFnsSt) {y y' : T ⟶ thickObj R I e G} (h : GlobalTheory.TorusCoord.im g y = 1)
    (χ : D.X) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val (g.t χ) (y * y').left z J = val (g.t χ) y.left z J * val (g.t χ) y'.left z J := by
  have k := GlobalTheory.TorusCoord.val_t_mul_points g hG χ y y' z J hJ
  have c : GlobalTheory.TorusCoord.cubeVal g χ z J y y' = 1 := by
    unfold GlobalTheory.TorusCoord.cubeVal
    rw [h]
    exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
  rwa [c, _root_.mul_one] at k

theorem coord_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {y y' : T ⟶ thickObj R I e G}
    (h : Coord g r a y) (h' : Coord g r a' y') : Coord g r (a * a') (y * y') := by
  refine ⟨by rw [GlobalTheory.TorusCoord.im_mul, h.1, h'.1, _root_.mul_one], fun χ z J hJ => ?_⟩
  exact (val_mul_of g hG h.1 χ z J hJ).trans
    ((congrArg₂ (· * ·) (h.2 χ z J hJ) (h'.2 χ z J hJ)).trans (map_mul _ _ _).symm)

theorem coord_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {y : T ⟶ thickObj R I e G}
    (h : Coord g r a y) : Coord g r a⁻¹ y⁻¹ := by
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul g y y⁻¹
    rw [mul_inv_cancel, GlobalTheory.TorusCoord.im_one, h.1, _root_.one_mul] at this
    exact this.symm
  · have k := (((GlobalTheory.TorusCoord.val_unit g χ hJ).symm.trans
      (GlobalTheory.TorusCoord.val_congr g χ (mul_inv_cancel y).symm z J)).trans (val_mul_of g hG h.1 χ z J hJ)).symm
    exact ((eq_inv_of_mul_eq_one_right k).trans (congrArg (·⁻¹) (h.2 χ z J hJ))).trans (map_inv _ _).symm
end

theorem comp_one_left {S : Scheme.{0}} (B : Over S) [GrpObj B] {T T' : Over S} (ρ : T' ⟶ T) :
    ρ.left ≫ (1 : T ⟶ B).left = (1 : T' ⟶ B).left :=
  congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)

theorem torPt_iff (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ)
    (x : TA R W ⟶ G) : U.TorPt a x ↔ ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (ρ : (Over.map (thick R I e)).obj T ⟶ TA R W) (y : T ⟶ thickObj R I e G),
      push I e G T y = ρ ≫ x → Coord (U.gt e) ρ.left a y := by
  constructor
  · intro h e T ρ y hy
    obtain ⟨h₁, h₂⟩ := h e T.left ρ.left y.left (congrArg (fun q => q.left) hy)
    refine ⟨Over.OverMorphism.ext (h₁.trans (comp_one_left D.P.A ρ)),
      fun χ z J hJ => Units.ext ((h₂ χ z J hJ).trans (gs_scal _ _ _))⟩
  · intro h e Z r xe hx
    let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (xe ≫ (thickObj R I e G).hom)
    have hw : r ≫ (TA R W).hom = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, Category.assoc]
      exact congrArg (xe ≫ ·) (Over.w (fstG I e G))
    let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W := Over.homMk r hw
    let y : T ⟶ thickObj R I e G := Over.homMk xe rfl
    obtain ⟨h₁, h₂⟩ := h e T ρ y (Over.OverMorphism.ext hx)
    exact ⟨(congrArg (fun q => q.left) h₁).trans (comp_one_left D.P.A ρ).symm,
      fun χ z J hJ => (congrArg Units.val (h₂ χ z J hJ)).trans (gs_scal _ _ _).symm⟩

section
variable (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]

theorem torPt_one : U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain rfl : y = 1 := push_inj e T (hy.trans ((MonObj.comp_one ρ).trans (map_one _).symm))
  exact coord_one _ _

theorem torPt_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {x x' : TA R W ⟶ G}
    (h : U.TorPt a x) (h' : U.TorPt a' x') : U.TorPt (a * a') (x * x') := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain ⟨p', hp'⟩ := push_surj e T (ρ ≫ x')
  obtain rfl : y = p * p' := push_inj e T (by rw [hy, map_mul, hp, hp', MonObj.comp_mul])
  exact coord_mul _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp) ((torPt_iff U _ _).1 h' e T ρ p' hp')

theorem torPt_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) : U.TorPt a⁻¹ x⁻¹ := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain rfl : y = p⁻¹ := push_inj e T (by rw [hy, map_inv, hp]; exact map_inv (preHom ρ) x)
  exact coord_inv _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp)

theorem torPt_pow (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) (k : ℕ) : U.TorPt (a ^ k) (x ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact torPt_one U
  | succ k ih => rw [pow_succ, pow_succ]; exact torPt_mul U hG ih h
end

end GlobalTheory.UU.TorMul

theorem GlobalTheory.UU.torPt_group : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W], U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 ∧ ∀ (a a' : Multiplicative D.X →* Wˣ) (x x' : TA R W ⟶ G), U.TorPt a x → (U.TorPt a' x' → U.TorPt (a * a') (x * x')) ∧ U.TorPt a⁻¹ x⁻¹ ∧ ∀ k : ℕ, U.TorPt (a ^ k) (x ^ k) :=
  fun hG _ _ _ _ _ _ _ _ _ U _ _ _ => ⟨TorMul.torPt_one U, fun _ _ _ _ h =>
    ⟨fun h' => TorMul.torPt_mul U hG h h', TorMul.torPt_inv U hG h, TorMul.torPt_pow U hG h⟩⟩

end
