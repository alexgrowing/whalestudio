import Mathlib
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
import GroundTheory.GlobalFields.SplittingFromInequality.Galois
import GroundTheory.GlobalFields.KummerTheory.Splitting
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationsForTripleStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SplitAway

open GroundTheory.Global Filter

theorem splitsCompletely_of_tower {K E M : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
    {u : HeightOneSpectrum (𝓞 K)} (h : SplitsCompletely M u) : SplitsCompletely E u := by
  intro w hw
  obtain ⟨W⟩ := GroundTheory.Global.nonempty_placesOver M w
  have h1 : W.1.asIdeal.LiesOver w.asIdeal := W.2
  have h2 : W.1.asIdeal.LiesOver u.asIdeal := Ideal.LiesOver.trans W.1.asIdeal w.asIdeal u.asIdeal
  obtain ⟨he, hf⟩ := h W.1 h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal W.1.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (R := 𝓞 K) w.asIdeal W.1.asIdeal] at hf
  exact ⟨(mul_eq_one.1 he).1, (mul_eq_one.1 hf).1⟩

theorem infinite_setOf_splitsCompletely (E : Type) [Field E] [NumberField E] :
    {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E u}.Infinite := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) := Algebra.IsAlgebraic.trans ℚ E (AlgebraicClosure E)
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := ⟨inferInstance, inferInstance⟩
  let M := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ (AlgebraicClosure E) := IsAlgClosure.isGalois ℚ _
  haveI : IsGalois ℚ M := IsGalois.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely ℚ M
  have hsub : {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely M u} ⊆
      {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E u} := fun u hu => splitsCompletely_of_tower (M := M) hu
  intro hfin
  have h0 := GroundTheory.Global.hasDirichletDensity_zero_of_finite (hfin.subset hsub)
  have e := tendsto_nhds_unique hd h0
  have hpos : (0 : ℝ) < 1 / (Module.finrank ℚ M : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := M)
    positivity
  exact hpos.ne' e

theorem primesOver_rat_eq (E : Type) [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 ℚ)) :
    u.asIdeal.primesOver (𝓞 E) = (u.asIdeal.under ℤ).primesOver (𝓞 E) := by
  have hs : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun x =>
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [eq_intCast, ← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    refine ⟨?_⟩
    rw [h.over, Ideal.under_under]
  · intro h
    refine ⟨Ideal.comap_injective_of_surjective _ hs ?_⟩
    change Ideal.under ℤ u.asIdeal = Ideal.under ℤ (Q.under (𝓞 ℚ))
    rw [Ideal.under_under, ← h.over]

end GlobalTheory.SplitAway

open GlobalTheory.SplitAway GroundTheory.Global in
theorem GlobalTheory.SplitAway.exists_splitsFully_notMem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (HeightOneSpectrum (𝓞 F))),
    ∃ v ∉ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ P
  classical
  obtain ⟨u, huS, huT⟩ := ((infinite_setOf_splitsCompletely E).diff
    (P.finite_toSet.image fun v : HeightOneSpectrum (𝓞 F) => v.under (𝓞 ℚ))).nonempty
  have hu : SplitsCompletely E u := huS
  obtain ⟨⟨v, hv⟩⟩ := GroundTheory.Global.nonempty_placesOver F u
  refine ⟨v, fun hP => huT ⟨v, hP, HeightOneSpectrum.ext hv.over.symm⟩, ?_, ?_⟩
  · show ((v.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = Module.finrank ℚ E
    have e1 : v.asIdeal.under ℤ = u.asIdeal.under ℤ := by
      rw [hv.over, Ideal.under_under]
    rw [e1, ← primesOver_rat_eq]
    exact (splitsCompletely_iff_ncard_primesOver E u).1 hu
  · have hF : SplitsCompletely E v := hu.of_liesOver v
    haveI := (splitsCompletely_iff_isFiniteSplit (L := E) v).1 hF
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun (v.adicCompletion F)
      (v.adicCompletion F ⊗[F] E)
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exfalso
        haveI : Subsingleton (v.adicCompletion F ⊗[F] E) := e.toEquiv.subsingleton
        have h1 : Module.finrank (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) = Module.finrank F E :=
          Module.finrank_baseChange
        rw [Module.finrank_zero_of_subsingleton] at h1
        exact (Module.finrank_pos (R := F) (M := E)).ne h1
      · exact h
    exact ⟨(((Pi.evalAlgHom (v.adicCompletion F) (fun _ : Fin n => v.adicCompletion F) ⟨0, hn⟩).comp
      e.toAlgHom).restrictScalars F).comp Algebra.TensorProduct.includeRight⟩
