import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DblDegree

theorem map_genericPoint_of_surjective {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Surjective f] : f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.surjective.range_eq, closure_univ] at h
  exact h

theorem exists_geomPoint_charZero {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {D : ℕ}
    (hp : IsArithVar p D) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K),
      Nonempty (Spec (CommRingCat.of K) ⟶ S) := by
  have := hp.isIntegral
  have h0 : CharZero Γ(S, ⊤) := (flat_int_iff_charZero _).1 hp.flat
  let F := S.functionField
  let K := AlgebraicClosure F
  have hinj : Function.Injective (S.germToFunctionField ⊤).hom := germ_injective_of_isIntegral S _ _
  have : CharZero F := charZero_of_injective_ringHom hinj
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ S.fromSpecStalk (genericPoint S)⟩⟩

theorem dbl_genericPoint_residueDegree : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k),
    IsRegSurf p → ∀ (P : PPAS S) (L : LB P.A.left), IsTheta P L → ∀ [IsIntegral P.A.left],
      dbl P (genericPoint P.A.left) = genericPoint P.A.left ∧
        (dbl P).residueDegree (genericPoint P.A.left) = 4 ^ P.g := by
  intro k _ S p hp P L hL _
  obtain ⟨hfin, hflat, hsurj⟩ :=
    GlobalTheory.PairKernel.mulA_finite_flat_surjective S hL.polAV 2 (by norm_num)
  have i1 : IsFinite (Out.mulA P.A 2).left := hfin
  have i2 : Flat (Out.mulA P.A 2).left := hflat
  have i3 : Surjective (dbl P) := hsurj
  have i4 : IsFinite (dbl P) := hfin
  have i5 : Flat (dbl P) := hflat
  have hgen := map_genericPoint_of_surjective (dbl P)
  refine ⟨hgen, ?_⟩
  rw [← CurveDegreesCompare.finrank_genericPoint (dbl P) hgen]
  have := hp.toIsArithVar.isLocallyNoetherian
  have hsm := P.isAb.smooth
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have : LocallyOfFinitePresentation (dbl P) := inferInstance
  obtain ⟨K, _, _, _, ⟨t⟩⟩ := exists_geomPoint_charZero hp.toIsArithVar
  let B := (Over.pullback t).obj P.A
  have hB : IsAbelianScheme B := Out.TLinPf.isAb_pullback t P.A P.isAb
  have : IsCommMonObj B := hB.comm
  have : Smooth B.hom := hB.smooth
  have hφ : (Over.pullback t).map (Out.mulA P.A 2) = 𝟙 B ^ 2 :=
    MulFiniteFlat.pullback_map_mulA t P.A 2
  have j1 : IsFinite ((Over.pullback t).map (Out.mulA P.A 2)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (AbLaw.MulN.isPullback_baseChange t _) i1
  have hu : IsUnit ((2 : ℕ) : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom 2]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 two_ne_zero)).map _
  have j2 : Etale ((Over.pullback t).map (Out.mulA P.A 2)).left := by
    rw [hφ]; exact GrpTangent.etale_id_pow B hu
  have hg : SmoothOfRelativeDimension P.g B.hom := by
    change SmoothOfRelativeDimension P.g (pullback.snd P.A.hom t)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback _ _) P.smoothDim
  let o : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B := 1
  let x : B.left := o.left (⊥ : PrimeSpectrum K)
  rw [(Scheme.Hom.isLocallyConstant_finrank (dbl P)).apply_eq_of_preconnectedSpace
    (genericPoint P.A.left) (pullback.fst P.A.hom t x)]
  have e1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ (AbLaw.MulN.isPullback_baseChange t (Out.mulA P.A 2)) x
  change Scheme.Hom.finrank (Out.mulA P.A 2).left _ = _
  rw [← e1, finrank_eq_card_kernel_points_of_etale K B hB _ x, hφ]
  have e2 : Nat.card {y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B // y ≫ 𝟙 B ^ 2 = 1} =
      Nat.card {y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B // y ^ 2 = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [pow_two, pow_two, MonObj.comp_mul, Category.comp_id]
  rw [e2, abMulN_holds K B P.g 2 hB hg (Nat.cast_ne_zero.2 two_ne_zero), pow_mul]
  norm_num

end GlobalTheory.DblDegree
