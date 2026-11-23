import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChangeStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.FEDesc

theorem spec_appTop_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  have e : (Spec.map (CommRingCat.ofHom f)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1.comp hf).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem toUnit_injective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact (Category.comp_id _).symm.trans a
  rw [e₂]
  exact (spec_appTop_injective _ (algebraMap (FractionRing R) F).injective).comp
    (spec_appTop_injective _ (IsFractionRing.injective R (FractionRing R)))

theorem famFE_of_sum {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k n : ℕ) (c : Fin n → F) (s : Raw D F k) (t : Fin n → Raw D F k)
    (h : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = ∑ i, gs r z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (t i α) r z J)
    (ht : ∀ i, DegPre.FamFE D F k (t i)) : DegPre.FamFE D F k s := by
  intro mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [h _ _ _ y J hJ, h _ _ _ y J hJ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (ht i mu α u hu hc) _ (𝟙 _) y J hJ, _root_.mul_assoc]
  congr 1
  have e : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have key : ∀ {Y : Scheme.{0}} (y : Y) (a : Y ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (x : F), a ≫ p = p →
      gs (𝟙 Y) y ⊤ (scal p x) = gs (𝟙 Y ≫ a) y ⊤ (scal p x) := by
    intro Y y a p x hap
    rw [← gs_pull (𝟙 Y) a y ⊤ trivial]
    conv_lhs => rw [← hap]
    rfl
  exact key y _ _ _ e

theorem fe_of_fe_kbar : GlobalFnsSt → AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ k : ℕ, U.FE (Kbar V) k → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], U.FE F k := by
  intro hG V _ _ _ hV D A G _ _ U k hK F _ _ t s hE
  obtain ⟨n, c, σ, f, hT, -, hs⟩ := hE
  have P := PullSec.pullEx V hV D A G U
  choose tK htK using fun i => ((P (Kbar V) (𝟙_ _) (toUnit _) k).1 (σ i)).exists
  choose sK hsK using fun i => ((P (Kbar V) (𝟙_ _) (toUnit _) k).2 (f i)).exists
  choose sF hsF using fun i => ((P F (𝟙_ _) (toUnit _) k).2 (f i)).exists
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  refine famFE_of_sum D F k n c s sF (fun α Z r z J hJ => ?_) fun i =>
    GlobalTheory.T.familyFunctionalEquation_field_change hG V D (𝟙_ _) k (f i) (Kbar V) F (toUnit _) (toUnit _) (sK i) (sF i) (toUnit_injective V _)
      (hsK i) (hsF i) (hK (tK i) (sK i)
        (IntExp.expF_of_expT V _ D A G U (Kbar V) k (σ i) (f i) (tK i) (sK i) (hT i) (htK i) (hsK i)))
  have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
    congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
  rw [hs α Z r (r ≫ (toUnit (TF (R := V) F) ▷ D.P.A).left) (by rw [Category.assoc, w]) z J hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg (_ * ·) ?_
  rw [IntExp.sval_comp (f i α) _ r z J hJ, ← hsF i α (r z) _ (fun ψ => hJ (r ≫ ψ)),
    ← IntExp.sval_comp (sF i α) _ r z J hJ, Category.comp_id]

end GlobalTheory.UU.FEDesc
end
