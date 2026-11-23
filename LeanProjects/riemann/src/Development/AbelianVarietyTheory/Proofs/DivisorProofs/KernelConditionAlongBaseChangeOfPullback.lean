import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrincSubring

section Transport

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {Z : Scheme.{0}} (f : Z ⟶ X')
    (z : Z) {k : L'.ι} (hk : f z ∈ L'.U k) : gm f z (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (f z))
  have e := hw Z f z j j k k hj hj hk hk
  rw [gm_self hL (f ≫ F) z hj, _root_.one_mul] at e
  exact inv_eq_one.1 (mul_eq_right.1 e.symm)

theorem trF_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {q : K → L'.ι} (hq : r z ∈ LB.wchart L' φ' q) :
    trF (L := L') φ' ε r z q q = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self_of_pGen hw hL (r ≫ φ' k) z (Set.mem_iInter.1 hq k), one_zpow]

theorem exists_down_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self_of_pGen hw hL _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

end Transport

theorem kerAlong_of_pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  intro S S' f A _ P A₁ _ P₁ φ φ₂ hP₁ h hs hw hK T a ha x hx
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨c, hc⟩ := hx
  let T' : Over S' := Over.mk a
  have hxw : x.left ≫ A₁.hom = a ≫ f := (Over.w x).trans ha.symm
  let x' : T' ⟶ A := Over.homMk (h.1.lift x.left a hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = x.left := h.1.lift_fst _ _ _
  have key : x' = 1 := hK T' x' <| by
    let b : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ T := Over.homMk (fst T' A).left (by
      show (fst T' A).left ≫ T.hom = (T' ⊗ A).hom ≫ f
      rw [← ha, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (fst T' A)))
    let c' : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ A₁ := pushPt h.1.w (snd T' A)
    have k₁ : (lift b c').left ≫ (fst T A₁).left = (fst T' A).left := congrArg (fun q => q.left) (lift_fst b c')
    have k₂ : (lift b c').left ≫ (snd T A₁).left = (snd T' A).left ≫ φ := congrArg (fun q => q.left) (lift_snd b c')
    have k₃ : (fst T' A ≫ x').left ≫ φ = (lift b c').left ≫ (fst T A₁ ≫ x).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc, k₁]
    have k₄ := GlobalTheory.SiegelDescent.lift_comp_square hs (T' := T' ⊗ A) (lift b c').left _ _ _ _ k₃ k₂.symm
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame P₁
      (fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left ≫ φ₂) _ _ (lift b c').left fun _ => k₄) c hc
    exact exists_down_of_pGen (φ' := fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left) (ε := fun _ => 1)
      ((isGen_iff w).1 hwg) hP₁ c₂ h₂
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) (by
    show 𝟙 T.left ≫ T.hom = a ≫ f
    rw [Category.id_comp, ha])
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext (by
    show 𝟙 T.left ≫ x.left = x'.left ≫ φ
    rw [Category.id_comp, hx'])
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A₁) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  have e₃ : 𝟙 T.left ≫ x.left = 𝟙 T.left ≫ (1 : T ⟶ A₁).left := congrArg (fun q => q.left) e₂
  exact Over.OverMorphism.ext (by simpa only [Category.id_comp] using e₃)

end GlobalTheory.PrincSubring
