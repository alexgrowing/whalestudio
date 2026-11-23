import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEtaleCompletionCompOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Desc.OpenChart

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x ∧
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨hx, ?_, ?_⟩
  · rw [hψ]
    exact GlobalTheory.TorRef.isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

theorem nonempty_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  intro E _ _ _ H Dw l Xo c S j _ A _ hA x hx
  obtain ⟨x', rfl⟩ := hx
  haveI : Smooth Xo.s := by haveI := Xo.smooth; exact SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI hreg : IsRegularLocalRing ((Xo.XF c).presheaf.stalk x') :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  obtain ⟨hcen, hEt, hres⟩ := completedStalk_chart (Xo.XF c) x'
  obtain ⟨ιF⟩ := GlobalTheory.GenFan.exists_ringHom_stalk c.F (Xo.XF c)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  set St := (Xo.XF c).presheaf.stalk x'
  set R := AdicCompletion (maximalIdeal St) St
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion St
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  let g : Sp R ⟶ Xo.XF c := GlobalTheory.fromSpecCompletedStalk (Xo.XF c) x'
  have hcz : CharZero R := (RingHom.charZero_iff ((algebraMap St R).comp ιF).injective).1 inferInstance
  have hb : Function.Bijective (j.stalkMap (g (closedPoint R))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨{
    R := R
    complete := inferInstance
    charZero := hcz
    ξ := g ≫ j
    centre := by
      show j (g (closedPoint R)) = j x'
      rw [hcen]
    etc := GlobalTheory.MemberEt.isEtaleCompletion_comp_openImmersion _ _ j R g hEt
    unr := by
      apply RingHom.FormallyUnramified.of_surjective
      rw [Scheme.stalkClosedPointTo_comp]
      exact hres.comp hb.2
    G := (Over.pullback g).obj A
    semi := IsSemiAbelian.pullback (f := g) A hA
    y := jK R ≫ g
    hy := Category.assoc _ _ _
    α := pullback.fst ((Over.pullback g).obj A).hom (jK R) ≫ pullback.fst A.hom g
    gen := IsGrpPullback.comp (isGrpPullback_pullback _ (jK R)) (isGrpPullback_pullback A g) }⟩

end GlobalTheory.Desc.OpenChart
