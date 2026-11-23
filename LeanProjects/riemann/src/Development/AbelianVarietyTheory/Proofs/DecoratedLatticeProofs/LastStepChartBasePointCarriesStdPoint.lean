import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameOnBaseCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.Mem.Col2.TopBase

theorem sel_under_of_mem_QE {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) {b : I.ι}
    {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q b) : I.sel (P.under (𝓞 B.fields.F)) = P := by
  unfold ColIn.Q Formalism.L2.Col.QE at hP
  split_ifs at hP with h
  · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hP
    congr 1
    exact HeightOneSpectrum.ext (hI.sel_ok w)
  · simp at hP

theorem topBase_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {C : Type} (chOf : (I.stp u a B.R.m).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N B.R.m))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a B.R.m).Cl → TC.GA B (B.R.N B.R.m)) (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E) (k : C → TC.GA B (B.R.N B.R.m)), I.Reads u a B.R.m chOf Lb U chi y st k → (∀ β, I.TopPt l Z u a (k β)) → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m, TC.PtOf (k β) q) ∧ ∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1 := by
  intro B X I hI hP l Z u a C chOf Lb U chi y st k hR hTop β
  have hPr := (base_fields_primes_ok B X).2.1
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    rw [Formalism.L2.Col.rank_X'_eq]
    have h1 := B.R.two_le_m
    have h2 : 1 ≤ B.R.t := B.R.t_odd.pos
    have h3 : 2 ≤ B.R.m * B.R.t := le_trans h1 (Nat.le_mul_of_pos_right _ h2)
    omega⟩
  refine ⟨⟨_, GlobalTheory.Mem.Col2.TopPtModel.topPt_base I l Z (hTop β)⟩, fun P hP hPa => ?_⟩
  obtain ⟨b, hb⟩ := (ColIn.mem_SQ I).1 hP
  have hq := (TwistPrimes.twist_primes_away I hI).2 u b P hb
  have hsP := sel_under_of_mem_QE I hI hb
  refine GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV P (hR.k_off β _ ?_ ?_ (Or.inr ?_))
  · exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv I hI hPr u b ⟨P, hb⟩
  · rintro ⟨P', hP', hv⟩
    have hsP' := sel_under_of_mem_QE I hI hP'
    apply hPa
    have e : P' = P := by rw [← hsP', ← hsP]; exact congrArg I.sel hv
    exact e ▸ hP'
  · intro j hj
    have hv : P.under (𝓞 B.host.F) ∈ Formalism.L2.Col.plUnder B.fields.F (B.primes X).vGs := by
      refine (Formalism.L2.Col.plUnder_vGs B.sp.cm hPr _).2 ?_
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
    obtain ⟨w, hw, hov⟩ := hv
    have hovP : Formalism.L2.Col.IsOver (P.under (𝓞 B.host.F)) P := rfl
    rcases Formalism.L2.Col.rll_over_cases B.sp.cm hovP hov with e | e
    · exact hq.1.2.1 (e ▸ hw)
    · exact hq.1.2.2.2.1 (e ▸ hw)

end GlobalTheory.Mem.Col2.TopBase
