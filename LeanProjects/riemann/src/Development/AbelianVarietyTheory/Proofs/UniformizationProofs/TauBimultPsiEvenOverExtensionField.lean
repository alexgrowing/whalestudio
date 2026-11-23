import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TauValues

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem comp_cT {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) (χ : D.X) :
    κ ≫ toUnit (TK R) ≫ D.c χ = cT D T χ := by
  rw [← Category.assoc, comp_toUnit]

theorem val_rigK {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.rigK κ.left z J = rigV D z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : κ.left ≫ (toUnit (TK R)).left = T.hom := by
    rw [← Over.comp_left, comp_toUnit]; rfl
  exact congrArg (fun q : T.left ⟶ Spec (CommRingCat.of R) =>
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig q z J) e

theorem bimult_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (a b m : D.X) :
    val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J ↔
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + b) m)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m))) κ.left z J =
      val (LB.mulGen D.P.L _ _ _ _ (D.tau a m) (D.tau b m)) κ.left z J := by
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left z J =
      cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) := by
    refine (val_cub D.cub κ hJ (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c m)).trans ?_
    rw [comp_cT, comp_cT, comp_cT]
  have l := (val_mul hJ (D.tau (a + b) m)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) c)
  have r := (val_mul hJ (D.tau a m) (D.tau b m) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) (val_tau D κ.left hJ _ _))
  rw [val_rigK D κ hJ] at l r
  rw [l, r]
  constructor <;> intro h <;> apply Additive.ofMul.injective <;> have e := congrArg Additive.ofMul h <;>
    simp only [ofMul_mul, ofMul_inv] at e ⊢ <;> linear_combination (norm := abel) e

theorem val_even {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (m : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.psi (-m)) (LB.pullGen D.P.L _ _ D.sym (D.xK m))) κ.left z J =
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
  have e : κ.left ≫ D.xK m = (cT D T m).left := by
    rw [← comp_cT D κ m]; rfl
  rw [e]

theorem bimult_iff' {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ a b m : D.X,
      val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J) ↔
    D.TauBimult :=
  ⟨fun h a b m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (bimult_iff D κ hJ a b m).1 (h z J hJ a b m),
    fun h _ _ hJ a b m => (bimult_iff D κ hJ a b m).2 (val_corr hJ (h a b m) κ.left)⟩

theorem even_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ m : D.X,
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J = val (D.psi m) κ.left z J) ↔ D.PsiEven :=
  ⟨fun h m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (val_even D κ hJ m).trans (h z J hJ m),
    fun h _ _ hJ m => (val_even D κ hJ m).symm.trans (val_corr hJ (h m) κ.left)⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  intro R _ _ D F _ _
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have hκ : κ.left = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) := rfl
  have : Flat κ.left := by
    rw [hκ]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField (FractionRing R)) _)
  have : Surjective κ.left := by
    have : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
    exact ⟨fun y => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩
  exact ⟨bimult_iff' D κ, even_iff D κ⟩

end GlobalTheory.TauValues
