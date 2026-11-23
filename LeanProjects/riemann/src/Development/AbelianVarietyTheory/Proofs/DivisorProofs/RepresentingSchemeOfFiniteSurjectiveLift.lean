import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenChartOfSmoothFamilyGeomFibreInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresentingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjectiveStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Assemble

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U Y : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : Y ⟶ U) :
    Fam A (ev M (fst A Y) (snd A Y ≫ u)) := by
  have hN : (ev M (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hN, (isAdditive_iff hN).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' _

omit [GrpObj A] in

theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) :
    evc hN (fst A Z) (snd A Z ≫ z ≫ y) = evc hM (fst A Z) (snd A Z ≫ z ≫ u) := by
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM y u).1 h)
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem exists_lift {S' : Over S} [IsFinite S'.hom] [Surjective S'.hom] {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ S) : Nonempty (Over.mk s ⟶ S') := by
  obtain ⟨t, ht⟩ := exists_lift_pt S'.hom s
  exact ⟨Over.homMk t ht⟩

theorem fibInj {B S' U : Over S} [IsFinite S'.hom] [Surjective S'.hom] {b : B ⟶ S'} {P : LB (A ⊗ B).left}
    (hP : Rep A b P) {M : LB (A ⊗ U).left} (hM : Fam A M) {j : U ⊗ S' ⟶ B} (hj : j ≫ b = snd U S')
    [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) : FibInj A M := by
  intro K _ _ s Y y u u' huu
  obtain ⟨t⟩ := exists_lift (S' := S') s
  have : Mono j := (Over.forget S).mono_of_mono_map (show Mono j.left from inferInstance)
  have k : ∀ v : Y ⟶ U, evc hM.isLB (fst A Y) (snd A Y ≫ v) =
      evc hP.fam.isLB (fst A Y) (snd A Y ≫ lift v (y ≫ t) ≫ j) := fun v ↦ by
    simpa only [lift_fst] using same_comp hM.isLB hP.fam.isLB h (lift v (y ≫ t))
  have hN := fam_ev hM u
  have e : lift u (y ≫ t) ≫ j = lift u' (y ≫ t) ≫ j := by
    refine (hP.univ Y (y ≫ t) _ hN).unique ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
      ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1 (k u)
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1
        (((same_iff hM.isLB hM.isLB u u').1 huu).trans (k u'))
  have e' := congrArg (· ≫ fst U S') ((cancel_mono j).1 e)
  simpa only [lift_fst] using e'

theorem exists_point {B S' U : Over S} {P : LB (A ⊗ B).left} (hP : P.IsLB) {M : LB (A ⊗ U).left} (hM : M.IsLB)
    {j : U ⊗ S' ⟶ B} [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) {K : Type} [Field K]
    {s : Sp K ⟶ S} {N : LB (A ⊗ Over.mk s).left} (hN : N.IsLB) (x : Over.mk s ⟶ B)
    (hx : LBIso N (ev P (fst A _) (snd A _ ≫ x))) (hr : x.left (default : PrimeSpectrum K) ∈ Set.range j.left) :
    ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  have hr' : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) z default]
  have fac := IsOpenImmersion.lift_fac j.left x.left hr'
  let v : Over.mk s ⟶ U ⊗ S' := Over.homMk (IsOpenImmersion.lift j.left x.left hr') (by
    rw [← Over.w j, ← Category.assoc, fac]; exact Over.w x)
  have hv : v ≫ j = x := Over.OverMorphism.ext fac
  refine ⟨v ≫ fst U S', (same_id_iff hN hM _).2 ((cls_eq_iff hN (pull_isLB hM _)).1 ?_)⟩
  rw [(cls_eq_iff hN (pull_isLB hP _)).2 hx, cls_ev hP, cls_ev hM, same_comp hM hP h v, hv]

theorem isPullback_prod (X Y : Over S) : IsPullback (fst X Y) (snd X Y) (toUnit X) (toUnit Y) :=
  ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
    (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit X))

end GlobalTheory.DualCon.Assemble

namespace GlobalTheory.DualCon
open Assemble

theorem hasRep_of_liftAt (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (B S' : Over (Sp R)) (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (hf : IsFinite S'.hom) (hs : Surjective S'.hom) (hP : Rep A b P)
    (hb : GlobalTheory.DualCon.Good g b.left) (hl : ∀ x : B.left, LiftAt A g b P x) : HasRep A g (𝟙_ _) := by
  choose U M j hM hU hj ho hx h using hl
  have hc : ∀ x, IsChart A (M x) := fun x ↦
    GlobalTheory.T.openChart_of_smoothFamily_geomFibreInjective R A g hA hg (U x) (M x) (hU x) (hM x) (fibInj hP (hM x) (hj x) (h x))
  obtain ⟨B₀, P₀, i, hP₀, hi, hcov, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing (Sp R) A hA B.left U M hc (by
    intro K _ _ s N hN
    obtain ⟨t⟩ := exists_lift (S' := S') s
    obtain ⟨x, ⟨-, hxN⟩, -⟩ := hP.univ _ t N hN
    exact ⟨_, exists_point hP.fam.isLB (hM _).isLB (h _) hN.isLB x hxN (hx _)⟩)
  have hsm : SmoothOfRelativeDimension g B₀.hom := by
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension g)
      (Scheme.Cover.mkOfCovers B.left (fun x ↦ (U x).left) (fun x ↦ (i x).left) hcov hi) fun x ↦ ?_
    have e : (i x).left ≫ B₀.hom = (U x).hom := Over.w _
    exact (congrArg (@SmoothOfRelativeDimension g _ _) e).mpr (hU x)
  have hpb := isPullback_prod B₀ S'
  obtain ⟨e, he, -⟩ := rep_unique (Sp R) A B (B₀ ⊗ S') S' b P _ _ hP
    (GlobalTheory.T.rep_ev_of_isPullback (Sp R) A B₀ _ S' _ _ P₀ _ _ _ hP₀ hpb)
  have hpb' : IsPullback (e.hom ≫ fst B₀ S') b (toUnit B₀) (toUnit S') :=
    hpb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [← he]) (by simp) (by simp)
  refine ⟨B₀, toUnit B₀, P₀, hP₀, GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective _ _ _ _ _ _ _ _ g (hpb'.map (Over.forget _)) ?_ ?_ ?_ hb⟩
  · exact (congrArg (@IsFinite _ _) (toUnit_left S')).mpr hf
  · exact (congrArg (@Surjective _ _) (toUnit_left S')).mpr hs
  · exact (congrArg (@SmoothOfRelativeDimension g _ _) (toUnit_left B₀)).mpr hsm

end GlobalTheory.DualCon
