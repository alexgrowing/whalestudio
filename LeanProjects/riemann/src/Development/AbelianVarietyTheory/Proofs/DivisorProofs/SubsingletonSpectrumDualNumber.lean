import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldHomFlatSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftMonoOfFpqcCoverLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFiniteTypeAgreementLocusInjectiveFamilStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem subsingleton_spectrum_dualNumber (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ (p : PrimeSpectrum (DualNumber K)) (x : DualNumber K), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro h
      have hsq : x * x = 0 := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h]
      exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => by rw [key p x, key q x])⟩

private theorem spMap_comp_of_eq {R₁ R₂ R₂' R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₂'] [CommRing R₃]
    {f : R₁ →+* R₂} {g : R₂ →+* R₃} {f' : R₁ →+* R₂'} {g' : R₂' →+* R₃} (h : g.comp f = g'.comp f') :
    spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tanLift_of_fieldChart : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [LocallyOfFiniteType U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → FieldChart A M →
      TanLift A M := by
  intro S A _ hA U _ M hM hInj hFC k _ s N hN u₀ h₀
  obtain ⟨hpull, -, -, hcomp, hev⟩ := GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A
  obtain ⟨ψ, hψ₁, hψ₂, hflat, hsurj⟩ :=
    GlobalTheory.T.dualNumber_fieldHom_flat_surjective k (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k))

  let T : Over S := Over.mk (spMap (dnInl k) ≫ s)
  haveI : IsNoetherianRing (DualNumber k) := inferInstance
  haveI : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  obtain ⟨G, π, hmono, -, hG⟩ := GlobalTheory.T.exists_mono_finiteType_agreement_locus_injective_family S A hA T U N M hN hM hInj
  haveI : Mono π.left := hmono

  let Y : Over S := Over.mk (spMap ψ ≫ spMap (dnInl k) ≫ s)
  let y : Y ⟶ T := Over.homMk (spMap ψ)
  have hq : spMap ψ ≫ spMap (dnInl k) =
      spMap (dnInl (AlgebraicClosure k)) ≫ spMap (algebraMap k (AlgebraicClosure k)) :=
    spMap_comp_of_eq hψ₁
  let q : Y ⟶ Over.mk (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) :=
    Over.homMk (spMap (dnInl (AlgebraicClosure k))) ((reassoc_of% hq) s).symm
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := hpull T Y N y hN
  obtain ⟨W, hW⟩ := hFC (AlgebraicClosure k) (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) Y q _ hN'

  let Z : Over S := Over.mk (spMap (dnFst (AlgebraicClosure k)) ≫ Y.hom)
  let z : Z ⟶ Y := Over.homMk (spMap (dnFst (AlgebraicClosure k)))
  have hr : spMap (dnFst (AlgebraicClosure k)) ≫ spMap ψ =
      spMap (algebraMap k (AlgebraicClosure k)) ≫ spMap (dnFst k) :=
    spMap_comp_of_eq hψ₂
  let e : Z ⟶ Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) :=
    Over.homMk (spMap (algebraMap k (AlgebraicClosure k))) ((reassoc_of% hr) (spMap (dnInl k) ≫ s)).symm
  have hez : e ≫ ptMap _ (dnFst k) = z ≫ y := by
    ext
    exact hr.symm
  have h₁ : Same A N M (z ≫ y) (e ≫ u₀) := by
    rw [← hez]
    exact hcomp T U _ Z N M (ptMap _ (dnFst k)) u₀ e hN.isLB hM.isLB h₀
  have h₂ : Same A (ev N (fst A Y) (snd A Y ≫ y)) M z (e ≫ u₀) :=
    (hev T U Y Z N M y z _ hN.isLB hM.isLB).2 h₁
  have hx : ∀ x, z.left x ∈ W := (hW Z z).1 ⟨_, h₂⟩

  haveI : Subsingleton Y.left := subsingleton_spectrum_dualNumber (AlgebraicClosure k)
  have x₀ : Z.left := IsLocalRing.closedPoint (AlgebraicClosure k)
  have hall : ∀ x : Y.left, x ∈ W := fun x => by
    rw [Subsingleton.elim x (z.left x₀)]
    exact hx x₀
  obtain ⟨u', hu'⟩ := (hW Y (𝟙 Y)).2 (fun x => hall _)
  have h₃ : Same A N M y u' := by
    have := (hev T U Y Y N M y (𝟙 Y) u' hN.isLB hM.isLB).1 hu'
    rwa [Category.id_comp] at this

  obtain ⟨z', hz'⟩ := (hG Y y).1 ⟨u', h₃⟩
  haveI : Flat (spMap ψ) := hflat
  haveI : Surjective (spMap ψ) := hsurj
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lift_mono_of_fpqc_cover_lift G.left T.left Y.left T.left π.left (𝟙 _) (spMap ψ) z'
    (by rw [Category.comp_id]; exact hz')
  exact (hG T (𝟙 T)).2 ⟨w, hw⟩

end GlobalTheory.DualOpen
