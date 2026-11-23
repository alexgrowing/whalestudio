import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaOverField

theorem exists_ne_zero_iff {K : Type} [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec) :
    (∃ j, th.f j ≠ 0) ↔ ThNZ th := by
  have := D₀.P.isAb.smooth
  have : IsReduced D₀.P.A.left := isReduced_scheme_of_smooth_of_isIntegrallyClosed K D₀.P.A.hom
  constructor
  · rintro ⟨j, hj⟩ y
    by_contra hn
    refine hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, ?_, ?_⟩))
    · exact Subsingleton.elim (α := PrimeSpectrum K) _ _
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz⟩
  · intro h
    obtain ⟨x, -, hx⟩ := h (IsLocalRing.closedPoint K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hj
    exact hj

theorem nonzero_generates : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec), ((∃ j, th.f j ≠ 0) ↔ ThNZ th) ∧ (ThNZ th → ∀ th' : D₀.P.L.Sec, ∃! r : K, ThMul r th th') ∧ ∃ th₀ : D₀.P.L.Sec, ThNZ th₀ := by
  intro hL _ K _ D₀ th
  refine ⟨exists_ne_zero_iff D₀ th, fun h th' => ?_, ?_⟩
  · have refl : LBIso D₀.P.L (D₀.P.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullUnpull D₀.P.L _ rfl) (chartPullId _)
        (exists_iso_linComb (F := 𝟙 D₀.P.A.left) D₀.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
    exact GlobalTheory.SectionBaseChange.generates hL.secBaseChange D₀.P (t := 𝟙 _) (φ := 𝟙 _)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) D₀.P.isLB refl th h th'
  · obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange D₀.P
    exact ⟨b, hb⟩

end GlobalTheory.ThetaOverField
