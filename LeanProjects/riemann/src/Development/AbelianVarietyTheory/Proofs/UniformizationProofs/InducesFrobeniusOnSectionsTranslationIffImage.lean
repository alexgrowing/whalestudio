import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_twist_iff {S : Scheme.{0}} {A T : Over S} [GrpObj A] (L : LB A.left) (ψ : T ⊗ A ⟶ T ⊗ A)
    (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (n : ℤ) {W : Type} (g : W → Prop)
    (P : W → (LB.Sec (LPow A L n T) → LB.Sec (LPow A L n T) → Prop) → Prop) :
    (∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α)) ↔
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ m hm n n α) := by
  subst hm
  rfl

theorem exists_smul_of_pt_eq (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℤ)
    (x : TFK (R := R) F ⟶ A.A) (α β : LB.Gen (thetaLB A.A A.L n x)) (hα : α.IsGen) (hβ : β.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (t : LB.Sec (LPow A.A A.L n (TFK (R := R) F)))
      (u u' : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A F) (LPow A.A A.L n (TFK (R := R) F))),
      IsActOf A.A A.L n ⟨x, α, hα⟩ t u → IsActOf A.A A.L n ⟨x, β, hβ⟩ t u' → u' = c • u := by
  obtain ⟨a, ha⟩ := H1.exists_const A.L A.isLB (fst (TFK (R := R) F) A.A).left (BoxTheta.surj_fst hG A.isAb _)
    (LB.mulGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] _ _ β
      (LB.invGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun t u u' hu hu' => ?_⟩
  · rintro rfl
    let z : (TFK (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TFK (R := R) F).left ⟶ A.A.left => exists_chart A.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (lift (𝟙 _) x).left z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (FieldBaseChange.gs_zero' _ z ⊤ trivial)
  · refine FieldBaseChange.SecOver.ext _ _ fun j => sec_ext_val A.isLB (fun y J hJ => ?_) j
    have e := (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _)))).symm.trans
      (ha _ (𝟙 _) y J hJ)
    refine (BoxTheta.act_val _ t u' hu' (𝟙 _) y hJ).trans (Eq.trans ?_
      (FieldBaseChange.sval_smul' hJ (𝟙 _) c u).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) e (BoxTheta.act_val _ t u hu (𝟙 _) y hJ).symm)
    exact (congrArg (fun v : ((TFK (R := R) F ⊗ A.A).left.presheaf.stalk y)ˣ => v.val * _)
      (inv_mul_cancel_right _ _).symm).trans ((congrArg (· * _) (Units.val_mul _ _)).trans (_root_.mul_assoc _ _ _))

theorem indAt_translT_iff : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ N hN p x
  have hG := hL.1.globalFns
  have key := fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ)
    (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s',
      U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D.toPre F N p w s s')
  constructor
  · rintro ⟨-, H⟩ w₀ hw₀
    obtain ⟨α, w, hα, hw, h⟩ := (key w₀).1 (H w₀ hw₀)
    refine ⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩
    rintro ⟨y, β, hβ⟩ rfl
    obtain ⟨c, hc, hcs⟩ := exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ
    obtain ⟨w', hw', hΦ⟩ := ProdTorsion.exists_phiRel_smul hG p w hw c hc
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t
    have e₁ := hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)
    have e₂ : s' = c • e u := ((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))
    exact e₂ ▸ e₁
  · intro H
    refine ⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩
    haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    obtain ⟨θ, rfl⟩ := BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1
    obtain ⟨w, hw, h⟩ := (H w₀ hw₀).2 θ rfl
    exact ⟨θ.φ, w, θ.isGen, hw, h⟩

end GlobalTheory.UT
