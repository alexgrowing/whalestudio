import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorInerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfLargeResidueChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholzeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwistsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostRamificationIdxEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpBoundFamilyLargeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageConditionsOfRankPartStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageThirdConditionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageSecondConditionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticUnitAtRamifiedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticZetaNeOneAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBoundStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

private theorem admPar_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (a : Fm.Ix x), AdmissibleParameterJ.AdmPar (Fm.L x a) := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  exact (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1

theorem GlobalTheory.NLinkE.main : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), GlobalTheory.NFacts.Facts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  intro hP eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.T.exists_localPositionData_off_exceptional_primes Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.T.jump_bound_family_large Fm
  obtain ⟨x3, h3⟩ := admPar_large Fm
  refine ⟨max (max x1 x2) x3, fun x hx' hx1 a hF => ?_⟩
  have hx : max x1 x2 ≤ x := le_trans (le_max_left _ _) hx'
  have hA := h3 x (le_trans (le_max_right _ _) hx') hx1 a
  have hJ := h2 x (le_trans (le_max_right _ _) hx) hx1 a hF
  intro k hl hg hexc _hW hHG r hr π hπ ρ hρ
  have hlp : (Fm.D x a).nd.l k |>.Prime := ((Fm.D x a).nd.lPrime k).out
  obtain ⟨⟨h5, ht, hq, hd, hsm⟩, hposition⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 a hJ _ hlp hl
  have hur := GlobalTheory.TripleGal.host_ramificationIdx_eq_one (Fm.D x a) _ hlp hsm hq hd
  have heps := GlobalTheory.AdmissibleDictionary.main (Fm.D x a) k
  obtain ⟨g1, gc, gss⟩ := GlobalTheory.T.image_conditions_of_rank_part _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g3 := GlobalTheory.T.big_image_third_condition _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g2 := GlobalTheory.T.big_image_second_condition hP.font _ _ _ k r π ρ hF hA hl hg hHG hr hπ hρ
  obtain ⟨gno, gunr⟩ := GlobalTheory.T.no_character_offset_unramified _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gS := GlobalTheory.T.quadratic_unit_at_ramified_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gQ := GlobalTheory.T.quadratic_zeta_ne_one_at_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition k r (fun _ => ρ) π := hρ.2
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia _ k r (fun _ => ρ) π hr g1 g3 gc gss gdec heps g3.2.2 hπ hur ht
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x a)
  have hTOP := GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar hP.bk hP.tate hP.euler (Fm.D x a) HW F Cm
  have hloc := GlobalTheory.UseLoc.main (Fm.D x a) HW F k r (fun _ => ρ) π hTOP (GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists _ HW F) hJ.1 hr hπ g2 g3 gc gdec heps h5 hsm hq hd
    (fun n _ up τ => hposition hexc _ ((Fm.D x a).nd.j_range k).1 ((Fm.D x a).nd.j_range k).2 n up τ)
  exact GlobalTheory.T.congruenceBound_extended_of_rationalBound _ k π ρ hπ (fun v hv => (gQ v hv).2)
    (fun hs hsha => GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit hP.artin _ k r _ π S hr hS hπ gno gunr gS gQ hloc hs hsha)
