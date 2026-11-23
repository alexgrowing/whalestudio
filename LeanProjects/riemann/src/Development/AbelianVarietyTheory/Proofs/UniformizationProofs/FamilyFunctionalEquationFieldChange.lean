import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecRelationDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FieldChange

theorem sval_extend {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {φ₁ : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hφ : φ₁ = fun k => h ≫ φ k)
    (s : LB.Sec (LB.LinComb L φ₁ ε)) (f : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ y J, Good L y J → sval s (𝟙 _) y J = sval f h y J) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J)
    (hJ : Good L z J) : sval s r z J = sval f (r ≫ h) z J := by
  subst hφ
  have e := sec_ext_val hL (s := s) (s' := DVR.pullSec L φ ε f h) (fun y J hJ => by
    rw [DVR.SectionScalarValuation.sval_pullSec φ ε f h _ y hJ, Category.id_comp]; exact H y J hJ)
  rw [← DVR.SectionScalarValuation.sval_pullSec φ ε f h r z hJ]
  exact congrArg (gs r z _) (e _)

theorem gs_scal_comp {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) (c : R) : gs (r ≫ h) z ⊤ (scal p c) = gs r z ⊤ (scal (h ≫ p) c) :=
  (gs_pull r h z ⊤ (by trivial) _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem fam_comp (φ : TF (R := R) F ⟶ T) (α : D.X) :
    DegPre.famφ D F α = fun i => (φ ▷ D.P.A).left ≫ famφT D T α i := by
  have e₀ : φ ▷ D.P.A ≫ snd T D.P.A = snd _ _ := whiskerRight_snd _ _
  have e₂ : φ ▷ D.P.A ≫ DVR.cP D _ α = DVR.cP D _ α := DVR.comp_cP D _ α
  funext i
  fin_cases i
  · exact (congrArg (fun q => q.left) e₀).symm
  · refine (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left)
      ((MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (DVR.cP D _ α)).trans ?_)).symm
    rw [e₀, e₂]; rfl
  · exact (congrArg (fun q => q.left) e₂).symm
  · exact (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (φ ▷ D.P.A))).symm

theorem tr_comp (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst _ _ ≫ DVR.cP D _ mu)).trans ?_
    rw [whiskerRight_snd, DVR.comp_cP, DVR.comp_cP]; rfl

theorem pullB_all {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α} {s : Raw D F k} (H : PullB D F φ k f s)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J :=
  sval_extend D.P.isLB _ (fam_comp D φ α) (s α) (f α) (H α) r z J hJ

theorem isUnit_scal {c : R} (hc : c ≠ 0) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) :
    IsUnit (gs r z ⊤ (scal (DegPre.BF D F).hom c)) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.assoc]; exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  have hu : IsUnit (scal (jK R) c) := by
    have n := congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    have hc' : IsUnit (algebraMap R (FractionRing R) c) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hc)
    exact (congrArg IsUnit n).mp (hc'.map _)
  rw [e, gs_eq _ _ ⊤ (by trivial)]
  exact ((hu.map ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F).appTop.hom).map _).map _

end FieldChange

open FieldChange in

theorem famFE_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  intro hG R _ _ _ D T _ k f F F' _ _ _ _ φ φ' s s' hinj hs hs' hfe mu α u' hu' hc'
  obtain ⟨u₀, r₁, r₂, hu₀, -, h₂, hv⟩ := GlobalTheory.UU.IntGen.main hG R D T k α mu
  obtain ⟨⟨u, hu, hc⟩, -⟩ := DVR.gen_fe (D := D) (F := F) hG k mu α
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  have sc : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T) (c : R)
      (y : (DegPre.BF D E).left), gs (ψ ▷ D.P.A).left y ⊤ (scal (T ⊗ D.P.A).hom c) =
        gs (𝟙 _) y ⊤ (scal (DegPre.BF D E).hom c) := fun ψ c y => by
    rw [← Over.w (ψ ▷ D.P.A), ← gs_scal_comp, Category.id_comp]
  have tr : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T),
      (ψ ▷ D.P.A).left ≫ (trT D (toUnit T ≫ D.c mu)).left = (𝟙 _ ≫ (DegPre.trF D E mu).left) ≫ (ψ ▷ D.P.A).left :=
    fun ψ => by rw [Category.id_comp]; exact congrArg (fun q => q.left) (tr_comp D ψ mu)
  have key := sec_relation_descends _ D.P.A T (TF (R := R) F) φ hinj _ _ D.P.L D.P.isLB _ _ _
    (famφT D T α) (DegPre.famε k) (famφT D T (α + k • mu)) (DegPre.famε k)
    (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k) (trT D (toUnit T ≫ D.c mu)).left
    (f α) (f (α + k • mu)) u₀ (scal (T ⊗ D.P.A).hom r₁) (scal (T ⊗ D.P.A).hom r₂) hu₀
    (fun U _ h => by
      refine Eq.symm (Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D (toUnit T ≫ D.c mu)).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h (famφT D T (α + k • mu) i) ^ DegPre.famε k i) rfl (DVR.prod_neg _ _ rfl))) ?_)
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (fun y J hJ => by
      have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hfe mu α u hu hc) _ (𝟙 _) y J hJ
      have e₂ := hv F φ u hu hc _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e₂
      rw [sc, sc, tr, ← pullB_all D hs α _ y J hJ, ← hs _ y J hJ, e₁, mul_left_comm, e₂, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_
  have e₁ := key _ (φ' ▷ D.P.A).left y J hJ
  have e₂ := hv F' φ' u' hu' hc' _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e₂
  rw [sc, sc, tr, ← pullB_all D hs' α _ y J hJ, ← hs' _ y J hJ, mul_left_comm, ← e₂, mul_left_comm] at e₁
  exact (isUnit_scal D h₂ _ y).mul_left_cancel e₁

end GlobalTheory
