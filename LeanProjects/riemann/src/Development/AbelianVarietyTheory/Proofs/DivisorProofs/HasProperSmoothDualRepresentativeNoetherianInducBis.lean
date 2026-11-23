import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeNoetherianInducStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenAffineOpenMeetingFibresGrpSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresPullbackSpecRingHomStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Step

theorem exists_sq_zero (R : Type) [CommRing R] [IsNoetherianRing R] (h : ¬ IsReduced R) :
    ∃ J : Ideal R, J ≠ ⊥ ∧ J ^ 2 = ⊥ := by
  classical
  set N := nilradical R with hNdef
  have hN : N ≠ ⊥ := by
    intro h0
    apply h
    refine ⟨fun x hx => ?_⟩
    have : x ∈ N := (mem_nilradical).2 hx
    rw [h0] at this
    exact (Submodule.mem_bot R).1 this
  have hnil : IsNilpotent N := IsNoetherianRing.isNilpotent_nilradical R
  let n := Nat.find hnil
  have hn : N ^ n = 0 := Nat.find_spec hnil
  have hn0 : n ≠ 0 := by
    intro h0
    have : N ^ 0 = 0 := h0 ▸ hn
    rw [pow_zero] at this
    apply hN
    rw [eq_bot_iff, ← Ideal.zero_eq_bot, ← this, Ideal.one_eq_top]
    exact le_top
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hN
    rw [hk] at hn
    simpa using hn
  refine ⟨N ^ k, ?_, ?_⟩
  · intro h0
    have := Nat.find_min hnil (show k < n by omega)
    exact this h0
  · rw [← pow_mul]
    apply le_bot_iff.1
    calc N ^ (k * 2) ≤ N ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by rw [← Nat.succ_eq_add_one, ← hk]; exact hn

theorem hasRep_opens {S X : Scheme.{0}} (i : X ⟶ S) [IsOpenImmersion i] (A : Over S) [GrpObj A] (g : ℕ)
    (V : S.Opens) (hV : (V : Set S) ⊆ Set.range i) (h : HasRep A g (Over.mk i)) : HasRep A g (Over.mk V.ι) := by
  have hr : Set.range V.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]; exact hV
  let m : Over.mk V.ι ⟶ Over.mk i := Over.homMk (IsOpenImmersion.lift i V.ι hr) (IsOpenImmersion.lift_fac _ _ _)
  exact GlobalTheory.T.baseChangeBis S A (Over.mk i) (Over.mk V.ι) g m h

theorem comap_ne_bot_away {R : Type} [CommRing R] (f : R) (J' : Ideal (Localization.Away f)) (h : J' ≠ ⊥) :
    J'.comap (algebraMap R (Localization.Away f)) ≠ ⊥ := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) y
  have hx : algebraMap R (Localization.Away f) x ∈ J' := by
    rw [← IsLocalization.mk'_spec (Localization.Away f) x s]
    exact J'.mul_mem_right _ hy
  have hx0 : algebraMap R (Localization.Away f) x ≠ 0 := by
    intro h0
    apply hy0
    rw [IsLocalization.mk'_eq_zero_iff]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ x).1 h0
  intro hb
  have : x ∈ J'.comap (algebraMap R (Localization.Away f)) := hx
  rw [hb, Submodule.mem_bot] at this
  exact hx0 (by rw [this, map_zero])

theorem hasRep_quot {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (ha : ∀ J' : Ideal R', J' ≠ ⊥ → J'.comap a ≠ ⊥) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap a) φ) (g : ℕ)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) :
    ∀ J' : Ideal R', J' ≠ ⊥ → HasRep A' g (Over.mk (spMap (Ideal.Quotient.mk J'))) := by
  intro J' hJ'
  set J := J'.comap a
  let q : R ⧸ J →+* R' ⧸ J' := Ideal.quotientMap J' a le_rfl
  have hq : q.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk J').comp a := by
    ext x; rfl
  have w : spMap q ≫ spMap (Ideal.Quotient.mk J) = (Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a)).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let m : Over.mk (spMap (Ideal.Quotient.mk J') ≫ spMap a) ⟶ Over.mk (spMap (Ideal.Quotient.mk J)) :=
    Over.homMk (spMap q) w
  have h1 := GlobalTheory.T.baseChangeBis _ A _ _ g m (hJ J (ha J' hJ'))
  exact ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap a) A A' φ hφ g (Over.mk (spMap (Ideal.Quotient.mk J')))).1).2 h1

theorem local_rep (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hJ : ∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) (s : Sp R) :
    ∃ V : (Sp R).Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι) := by
  obtain ⟨f, hs, W, hW, hWf⟩ := GlobalTheory.T.exists_basicOpen_affineOpen_meeting_fibres_grpScheme R A s
  let a := algebraMap R (Localization.Away f)
  let A' := (Over.pullback (spMap a)).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hφ : IsGrpPullback A' A (spMap a) (pullback.fst _ _) := isGrpPullback_pullback A (spMap a)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback a A A' _ g hφ hA hg
  obtain ⟨V, hV, hVs⟩ := GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom a A W hW hWf
  haveI : @Algebra.FiniteType ℤ (Localization.Away f) _ _ (Ring.toIntAlgebra _) := by
    have h := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ R)
      (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) (Localization.Away f))
    convert h using 1 <;> first | rfl | exact Subsingleton.elim _ _
  have h1 : HasRep A' g (𝟙_ _) :=
    GlobalTheory.T.hasProperSmoothDualRepresentative_noetherianInduction (Localization.Away f) A' g hA' hg' V hV hVs
      (hasRep_quot a (comap_ne_bot_away f) A A' _ hφ g hJ)
  have h2 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap a) A A' _ hφ g (𝟙_ _)).1).1 h1
  have h3 : HasRep A g (Over.mk (spMap a)) := by
    convert h2 using 2 <;> first | rfl | exact (Category.id_comp _).symm
  have : IsOpenImmersion (spMap a) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨(spMap a).opensRange, hs, hasRep_opens (spMap a) A g _ (fun x hx => hx) h3⟩

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  by_cases hr : IsReduced R
  · exact GlobalTheory.T.hasProperSmoothDualRepresentative_of_local _ A g hA (local_rep R A g hA hg hJ)
  · obtain ⟨J, hJ0, hJ2⟩ := exists_sq_zero R hr
    exact GlobalTheory.T.hasProperSmoothDualRepresentative_of_sqZero R A g hA hg J hJ2 (hJ J hJ0)

end GlobalTheory.DualCon.Step
