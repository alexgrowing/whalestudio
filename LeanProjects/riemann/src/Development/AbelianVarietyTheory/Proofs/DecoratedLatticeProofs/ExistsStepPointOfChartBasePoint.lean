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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatEqOfCarries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.KxPoint

theorem pointOf_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {C : Type} (chOf : (I.stp u a i).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → TC.GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : C → TC.GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf (k β) q) → (∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1) → ∃ (b0 : Idx I.sel (I.tup a) (I.idx a) i) (p0 : PtAt B.R I.sel (I.tup a) (I.cst a) u i), TC.PtOf (k β) (extTo I.SQ p0.1.1) ∧ p0.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) ∧ ∀ c, chOf c = β → c.1 = b0 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn p0 := by
  intro B X I hI hP u a i hi C chOf Lb U chi y st k hR β hq hk
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  have hd := ChEx.q_disj I hI a
  obtain ⟨c₀, hc₀⟩ := hR.onto β
  obtain ⟨q, hqk⟩ := hq
  obtain ⟨p, hpk, hpN⟩ := hR.k_std β
  have hqN : q.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) := by
    rw [← hpN]
    exact GlobalTheory.BaseCosetPt.lat_eq_of_carries q.deco.2.lat p.deco.2.lat hqk.lat hpk.lat
  obtain ⟨r', hr'1, hr'2, hr'3⟩ := ChExM.exists_pt_inv hd ((I.stp u a i).rep c₀) q
  have hcos : cosetIn r' = cosetIn ((I.stp u a i).rep c₀) :=
    (ChExM.cosetIn_iff hd (MemChart.hqG hPr) _ _).2 ⟨hr'2, hr'3⟩
  refine ⟨c₀.1, r', ?_, ?_, ?_⟩
  · rw [hr'1]
    refine ⟨hqk.uni, hqk.lat, hqk.f, hqk.be, fun P i' j => ?_⟩
    rw [extTo_fr]
    by_cases hPQ : P.1 ∈ I.Q a
    · rw [ptFr_of_mem q (hd P.1 hPQ) hPQ]
      exact hqk.fr ⟨P.1, hPQ⟩ i' j
    · have hPG : P.1 ∉ (B.primes X).vGs := by
        obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 P.2
        exact ChEx.q_disj I hI b P.1 hb
      have hfr : ptFr q P.1 = 1 := by
        unfold ptFr
        rw [dif_neg hPG, dif_neg hPQ, hqN]
        unfold GlobalTheory.Mem.Col2.latFr
        exact if_pos rfl
      have hkP := congrFun (congrFun (hk P.1 P.2 hPQ) i') j
      rw [hfr]
      simp only [Matrix.map_apply] at hkP
      rw [hkP]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [hr'1]; exact hqN
  · intro c hc
    obtain ⟨h1, h2⟩ := (hR.key c c₀).1 (hc.trans hc₀.symm)
    exact ⟨h1, h2.trans hcos.symm⟩

end GlobalTheory.KxPoint
