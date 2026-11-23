import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

namespace GlobalTheory.FormalAlg

structure Charts {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) where

  D : ∀ e, Fin (n + 1) → (Y e).left.Opens

  aff : ∀ e i, IsAffineOpen (D e i)

  cover : ∀ e, ⨆ i, D e i = ⊤

  pre : ∀ e i, β e ⁻¹ᵁ D (e + 1) i = D e i

  ρ : ∀ e i, Fin (n + 1) → Γ((Y e).left, D e i)

  ρ_pull : ∀ e i j, ((β e).appLE (D (e + 1) i) (D e i) (pre e i).ge).hom (ρ (e + 1) i j) = ρ e i j

  ρ_self : ∀ i, ρ 0 i i = 1

  basic : ∀ i j, (Y 0).left.basicOpen (ρ 0 i j) = D 0 i ⊓ D 0 j

  cocycle : ∀ i j l, rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i l) =
    rs (Y 0).left (inf_le_left : D 0 i ⊓ D 0 j ≤ D 0 i) (ρ 0 i j) *
      rs (Y 0).left (inf_le_right : D 0 i ⊓ D 0 j ≤ D 0 j) (ρ 0 j l)

  surj : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (cst (Y 0).hom (D 0 i)) (ρ 0 i))

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}

def towerIdeal (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (J : Ideal R)
    (V : (Y e).left.Opens) : Ideal Γ((Y e).left, V) :=
  J.map (cst ((Y e).hom ≫ thick R I e) V)

def Charts.ev (C : Charts I Y β n) (e : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →+* Γ((Y e).left, C.D e i) :=
  MvPolynomial.eval₂Hom (cst ((Y e).hom ≫ thick R I e) (C.D e i)) (C.ρ e i)

def Charts.point (R : Type) [CommRing R] (I : Ideal R) :
    Charts I (fun e => Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))) (fun e => thickTrans R I e) 0 where
  D _ _ := ⊤
  aff _ _ := isAffineOpen_top (Spec _)
  cover _ := by simp
  pre _ _ := rfl
  ρ _ _ _ := 1
  ρ_pull _ _ _ := map_one _
  ρ_self _ := rfl
  basic _ _ := by simp
  cocycle _ _ _ := by simp
  surj _ := fun y => by
    obtain ⟨a, ha⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))))) rfl).2 y
    exact ⟨MvPolynomial.C a, (MvPolynomial.eval₂Hom_C _ _ _).trans ha⟩

@[simp] theorem Charts.ev_X (C : Charts I Y β n) (e : ℕ) (i j : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X j) = C.ρ e i j := by
  rw [Charts.ev]
  exact MvPolynomial.eval₂Hom_X' _ _ _

@[simp] theorem Charts.ev_C (C : Charts I Y β n) (e : ℕ) (i : Fin (n + 1)) (r : R) :
    C.ev e i (MvPolynomial.C r) = cst ((Y e).hom ≫ thick R I e) (C.D e i) r := by
  rw [Charts.ev]
  exact MvPolynomial.eval₂Hom_C _ _ _

theorem Charts.ρ_mul_ρ (C : Charts I Y β n) (i j : Fin (n + 1)) :
    rs (Y 0).left (inf_le_left : C.D 0 i ⊓ C.D 0 j ≤ C.D 0 i) (C.ρ 0 i j) *
      rs (Y 0).left (inf_le_right : C.D 0 i ⊓ C.D 0 j ≤ C.D 0 j) (C.ρ 0 j i) = 1 := by

  have h := C.cocycle i j i
  rw [C.ρ_self, map_one] at h
  exact h.symm

theorem Charts.le_of_isUnit (C : Charts I Y β n) {i j : Fin (n + 1)} (h : IsUnit (C.ρ 0 i j)) :
    C.D 0 i ≤ C.D 0 j := by

  have h1 := (Y 0).left.basicOpen_of_isUnit h
  rw [C.basic] at h1
  exact inf_eq_left.mp h1

section Projective

open GlobalTheory.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

theorem rs_app {X Z : Scheme.{0}} (b : Z ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : b ⁻¹ᵁ V ≤ b ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs Z h' ((b.app U).hom x) = (b.app V).hom (rs X h x) := by
  exact (congrArg (fun φ => φ.hom x) (b.naturality (homOfLE h).op)).symm

def Charts.ofVeryAmple {R : Type} [CommRing R] (I : Ideal R) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {H : LB X} {n : ℕ} {s : Fin (n + 1) → H.Sec} (hs : VeryAmpleBy f H s)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X)
    (hb : ∀ e, IsPullback (b e) (Y e).hom f (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e) :
    Charts I Y β n where
  D e i := b e ⁻¹ᵁ nonzeroLocus (s i)
  aff e i := by
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (b e) := MorphismProperty.of_isPullback (hb e).flip this
    exact (hs.2 i).1.preimage (b e)
  cover e := by rw [← Scheme.Hom.preimage_iSup, hs.1]; rfl
  pre e i := by rw [← Scheme.Hom.comp_preimage, hβ]
  ρ e i j := ((b e).app _).hom (secRatio (s i) (s j))
  ρ_pull e i j := by
    have key : ∀ (c : (Y e).left ⟶ X) (hc : β e ≫ b (e + 1) = c) (h), ((β e).appLE (b (e + 1) ⁻¹ᵁ nonzeroLocus (s i))
        (c ⁻¹ᵁ nonzeroLocus (s i)) h).hom (((b (e + 1)).app _).hom (secRatio (s i) (s j))) =
        (c.app _).hom (secRatio (s i) (s j)) := by
      rintro _ rfl h
      exact rs_self _ _
    exact key _ (hβ e) _
  ρ_self i := by rw [secRatio_self, map_one]
  basic i j := by
    have := Scheme.preimage_basicOpen (b 0) (secRatio (s i) (s j))
    rw [basicOpen_secRatio] at this
    exact this.symm
  cocycle i j l := by
    have e := congrArg ((b 0).app (nonzeroLocus (s i) ⊓ nonzeroLocus (s j))).hom
      (secRatio_mul_secRatio (s i) (s j) (s l) inf_le_left inf_le_right)
    rw [map_mul] at e
    exact (rs_app (b 0) inf_le_left _ _).trans (e.symm.trans
      (congrArg₂ (· * ·) (rs_app (b 0) inf_le_left _ _).symm (rs_app (b 0) inf_le_right _ _).symm))
  surj i := fun y => by
    obtain ⟨x, rfl⟩ := SmallExtLift.app_surj Ideal.Quotient.mk_surjective (hb 0) (hs.2 i).1 y
    obtain ⟨r, hr, hsurj⟩ := (hs.2 i).2
    obtain rfl : r = fun j => secRatio (s i) (s j) := funext fun j => eq_secRatio _ _ (hr j)
    obtain ⟨p, rfl⟩ := hsurj x
    refine ⟨MvPolynomial.map (Ideal.Quotient.mk _) p, ?_⟩
    rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
    congr 2
    ext a
    exact (SmallExtLift.app_cst (hb 0).w _ a).symm

def Charts.projSpace (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) :
    Charts I (fun e => thickObj R I e (Over.mk (PSpace.str R n))) (fun e => thickMap R I e _) n :=
  Charts.ofVeryAmple I (PSpace.str R n) (H := O1 R n) (s := coord R n)
    ((veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R n, by rw [toProj_coord]; infer_instance⟩)
    _ _ (fun e => pullback.fst (PSpace.str R n) (thick R I e)) (fun _ => IsPullback.of_hasPullback _ _)
    (fun _ => (pullback.lift_fst _ _ _).trans (Category.comp_id _))

def Charts.projective (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) :
    Charts I (fun e => Over.mk (PSpace.str (R ⧸ I ^ (e + 1)) n))
      (fun e => baseChange n (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))) n where
  D e i := chart (R ⧸ I ^ (e + 1)) n i
  aff e i := isAffineOpen_chart _ n i
  cover e := iSup_chart _ n
  pre e i := baseChange_preimage_chart n _ i
  ρ e i j := ratio (R ⧸ I ^ (e + 1)) n i j
  ρ_pull e i j := by
    have h := baseChange_app_ratioOn
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (e + 1))))
      (le_refl (chart (R ⧸ I ^ (e + 1 + 1)) n i)) j
    exact (congrArg (rs (PSpace (R ⧸ I ^ (e + 1)) n)
      (baseChange_preimage_chart n _ i).ge) h).trans rfl
  ρ_self i := ratioOn_self
  basic i j := basicOpen_ratioOn
  cocycle i j l := (ratioOn_mul_ratioOn (U := chart _ n i ⊓ chart _ n j)
    (hi := inf_le_left) (hj := inf_le_right)).symm
  surj i := aeval_ratio_surjective _ n i

attribute [local instance] ProjSpace.algebraSections in

theorem Charts.projective_not_isUnit (R : Type) [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) (e : ℕ) :
    ¬ IsUnit ((Charts.projective R I 1).ρ e 0 1) := by
  have hne : I ^ (e + 1) ≠ ⊤ := by
    intro h
    apply hI
    rw [eq_top_iff, ← h]
    exact Ideal.pow_le_self (Nat.succ_ne_zero e)
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.mpr hne
  intro hu

  have hr : IsUnit (chartAlgEquiv (R ⧸ I ^ (e + 1)) 1 0 (MvPolynomial.X ⟨1, by decide⟩)) := by
    rw [chartAlgEquiv_X]
    exact hu
  have hu' := (hr.map (chartAlgEquiv (R ⧸ I ^ (e + 1)) 1 0).symm).map
    (MvPolynomial.eval fun _ => (0 : R ⧸ I ^ (e + 1)))
  rw [AlgEquiv.symm_apply_apply, MvPolynomial.eval_X] at hu'
  exact not_isUnit_zero hu'

theorem Charts.projective_D_ne (R : Type) [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    (Charts.projective R I 1).D 0 0 ≠ (Charts.projective R I 1).D 0 1 := by

  intro h
  apply Charts.projective_not_isUnit R I hI 0
  show IsUnit (ratio (R ⧸ I ^ (0 + 1)) 1 0 1)
  exact ⟨ratioUnit (chart (R ⧸ I ^ (0 + 1)) 1 0) 0 1 le_rfl h.le, val_ratioUnit⟩

end Projective

end GlobalTheory.FormalAlg
