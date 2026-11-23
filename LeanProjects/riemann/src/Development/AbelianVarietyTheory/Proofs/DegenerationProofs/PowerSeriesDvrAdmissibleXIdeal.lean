import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsComplexCmAbelianObjectStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPelUniformisationCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ConstantFamily

theorem cDvr_powerSeries : GlobalTheory.LN.CDvr (PowerSeries ℂ) :=
  ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
    algebraRat.charZero _⟩

theorem powerSeries_dvr_admissible_X_ideal : GlobalTheory.LN.admitted (PowerSeries ℂ) (IsLocalRing.maximalIdeal _) := by
  have h := cDvr_powerSeries
  have := h.2.1
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance, h.2.2, inferInstance, ?_⟩
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal (PowerSeries ℂ))
  infer_instance

theorem exists_pelUnif_powerSeries :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∃ (t : SAB H (Sp (PowerSeries ℂ))) (P : PELUnif (IsLocalRing.maximalIdeal (PowerSeries ℂ)) t), P.TorsionIso ∧ P.A.g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ 0 < P.A.g ∧ GlobalTheory.LN.CDvr (PowerSeries ℂ) ∧ GlobalTheory.LN.PolAt t (Out.jK (PowerSeries ℂ)) ∧ GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal _) ∧ GlobalTheory.LN.ThetaNZ t.G t.PP.L ∧ GlobalTheory.LN.admitted (PowerSeries ℂ) (IsLocalRing.maximalIdeal _) := by
  intro E _ _ _ H D hD
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  obtain ⟨l, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E H 1 one_pos
  obtain ⟨b, o, -, -, hd, -⟩ := GlobalTheory.T.exists_complex_cm_abelian_object E H D hD l
  let f : Sp (PowerSeries ℂ) ⟶ Sp ℂ := spMap (PowerSeries.C (R := ℂ))
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp (PowerSeries ℂ)), Nonempty (SABMap t o.t f) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f o.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m', -⟩ := ObjMaps.exists_sab_id o.t
  have hpol : GlobalTheory.LN.PolAt t (Out.jK (PowerSeries ℂ)) :=
    GlobalTheory.LN.GenericPoint.polAt_of_lift m m' o.proper o.ample o.ktriv _ (Out.jK (PowerSeries ℂ) ≫ f) (Category.comp_id _)
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 o.proper
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  have hs : GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal _) :=
    ⟨_, ZJ.isGt_splitExtOfAbelian _ (isAbelianScheme_pullback_obj _ t.G hab)⟩
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h₁ h₂ E H _ t hpol
  obtain ⟨P, hPA, -, hP⟩ := GlobalTheory.UU.exists_pelUnif_of_cdvr_unconditional E H _ cDvr_powerSeries t A gen hgen hL hs
  have hst := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (Module.finrank ℚ E / 2 * (D.p + D.q))
  have hdt : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) t.G.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension _) m.cart.1 hd
  have hdA : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.A.hom := by
    have : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))
        ((Over.pullback (Out.jK (PowerSeries ℂ))).obj t.G).hom :=
      hst.of_isPullback (IsPullback.of_hasPullback t.G.hom (Out.jK (PowerSeries ℂ))) hdt
    have hi : IsIso gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
    exact hst.of_isPullback (IsPullback.of_horiz_isIso (fst := gen.inv.left) (g := 𝟙 _)
      ⟨(Over.w gen.inv).trans (Category.comp_id _).symm⟩) this
  have hg : P.A.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
    rw [hPA]
    exact H1.dim_unique _ A.smoothDim hdA (eSec A.A (IsLocalRing.closedPoint _))
  have h2 : 2 ≤ Module.finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two _ E]
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  refine ⟨t, P, hP, hg, ?_, cDvr_powerSeries, hpol, hs,
    GlobalTheory.ThetaDvr.thetaNZ_of_polAt h₁ h₂ E H _ t hpol, powerSeries_dvr_admissible_X_ideal⟩
  rw [hg]
  exact Nat.mul_pos (by omega) hD

end GlobalTheory.ConstantFamily
