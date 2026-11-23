import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadOfPolarizedFiberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolNear

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem polAt_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' : Type} [CommRing R]
    [IsDomain R] [CommRing R'] [IsDomain R'] (b : R →+* R') (hb : Function.Injective b) {t : SAB H (Sp R)}
    {t' : SAB H (Sp R')} (m : SABMap t' t (spMap b)) (hp : GlobalTheory.LN.PolAt t (jK R)) : GlobalTheory.LN.PolAt t' (jK R') := by
  have hi : Function.Injective ((algebraMap R' (FractionRing R')).comp b) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hb
  refine GlobalTheory.DatUniq.polAt_pull m hp (jK R') (spMap (IsFractionRing.lift (K := FractionRing R) hi)) ?_
  have e : (IsFractionRing.lift (K := FractionRing R) hi).comp (algebraMap R (FractionRing R)) =
      (algebraMap R' (FractionRing R')).comp b :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := FractionRing R) hi x
  have e' := congrArg spMap e
  rw [spMap_comp' (algebraMap R (FractionRing R)) (IsFractionRing.lift (K := FractionRing R) hi),
    spMap_comp' b (algebraMap R' (FractionRing R'))] at e'
  exact e'

theorem exists_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], IsIntegrallyClosed R → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ r : R, g r ≠ 0 ∧ ∃ (t' : SAB H (Sp (Localization.Away r))) (_ : SABMap t' t (spMap (algebraMap R (Localization.Away r)))), IsProper t'.G.hom ∧ RelAmple t'.G t'.PP.L ∧ KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t hgen C _ g hp

  have hsub : Set.range (spMap g) ⊆ abLocus t.G := abLocusOne _ t.G t.semi C (spMap g) hp.1
  have hop : IsOpen (abLocus t.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum C) := inferInstance
  obtain ⟨_, ⟨r₁, rfl⟩, hq, hsub₁⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (hsub ⟨y, rfl⟩) hop
  have hg₁ : g r₁ ≠ 0 := by
    intro h0
    refine (PrimeSpectrum.mem_basicOpen _ _).1 hq ?_
    show g r₁ ∈ y.asIdeal
    rw [h0]; exact zero_mem _
  have hr₁ : r₁ ≠ 0 := fun h => hg₁ (by rw [h, map_zero])
  let R₁ := Localization.Away r₁
  have hM₁ : Submonoid.powers r₁ ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr₁
  haveI : IsDomain R₁ := IsLocalization.isDomain_localization hM₁
  haveI : IsNoetherianRing R₁ := IsLocalization.isNoetherianRing (Submonoid.powers r₁) R₁ inferInstance
  have hinj₁ : Function.Injective (algebraMap R R₁) := IsLocalization.injective R₁ hM₁

  obtain ⟨t₁, ⟨m₁⟩⟩ := exists_sab (spMap (algebraMap R R₁)) t
  have hab : abLocus t₁.G = Set.univ := Set.eq_univ_of_forall fun x =>
    (abLocus_pullback abLocusOne t.semi m₁.cart.1 x).1 (hsub₁ (by
      have hx : spMap (algebraMap R R₁) x ∈ Set.range (PrimeSpectrum.comap (algebraMap R R₁)) := ⟨x, rfl⟩
      rwa [PrimeSpectrum.localization_away_comap_range R₁ r₁] at hx))
  have hgen₁ : GlobalTheory.LN.PolAt t₁ (jK R₁) := polAt_generic _ hinj₁ m₁ hgen
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj₁
  have hP₁ : IsProper t₁.G.hom := GlobalTheory.T.proper_of_abelian_everywhere E H R₁ t₁ hgen₁ hab

  let g₁ : R₁ →+* C := IsLocalization.Away.lift r₁ (Ne.isUnit hg₁)
  have hgg : g₁.comp (algebraMap R R₁) = g := IsLocalization.lift_comp _
  have hp₁ : GlobalTheory.LN.PolAt t₁ (spMap g₁) :=
    GlobalTheory.DatUniq.polAt_pull m₁ hp (spMap g₁) (𝟙 _) (by rw [Category.id_comp, ← spMap_comp', hgg])

  obtain ⟨s, hs, hamp⟩ := GlobalTheory.T.relative_ample_spread_of_polarized_fiber E H R₁ t₁ hP₁ C g₁ hp₁
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r₁) s
  simp only at ha

  have hga : g a ≠ 0 := by
    have e : g a = g₁ s * g (r₁ ^ n) := by rw [← hgg, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, ha]
    rw [e, map_pow]
    exact mul_ne_zero hs (pow_ne_zero _ hg₁)
  have hgr : g (r₁ * a) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hg₁ hga
  have hr : r₁ * a ≠ 0 := fun h0 => hgr (by rw [h0, map_zero])
  refine ⟨r₁ * a, hgr, ?_⟩

  let R' := Localization.Away (r₁ * a)
  have hM : Submonoid.powers (r₁ * a) ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr
  haveI : IsDomain R' := IsLocalization.isDomain_localization hM
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers (r₁ * a)) R' inferInstance
  have hinj : Function.Injective (algebraMap R R') := IsLocalization.injective R' hM
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  have hu : IsUnit (algebraMap R R' (r₁ * a)) := IsLocalization.Away.algebraMap_isUnit (r₁ * a)
  rw [map_mul] at hu
  let h : R₁ →+* R' := IsLocalization.Away.lift r₁ (isUnit_of_mul_isUnit_left hu)
  have hh : h.comp (algebraMap R R₁) = algebraMap R R' := IsLocalization.lift_comp _
  have hhs : IsUnit (h s) := by
    have e : h s * algebraMap R R' (r₁ ^ n) = algebraMap R R' a := by
      rw [← hh, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, ha]
    exact isUnit_of_mul_isUnit_left (e ▸ isUnit_of_mul_isUnit_right hu)

  obtain ⟨t', ⟨m'⟩⟩ := exists_sab (spMap h) t₁
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ t t₁ t' _ _ m₁ m'
  have ee : spMap h ≫ spMap (algebraMap R R₁) = spMap (algebraMap R R') := by rw [← spMap_comp', hh]
  have hP' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hP₁
  have hA' : RelAmple t'.G t'.PP.L := hamp R' h hhs t' m'
  exact ⟨t', ee ▸ n', hP', hA', GlobalTheory.T.canonical_trivial_of_relative_ample E H R' t' hP' hA' (polAt_generic _ hinj (ee ▸ n') hgen)⟩

end GlobalTheory.PolNear
