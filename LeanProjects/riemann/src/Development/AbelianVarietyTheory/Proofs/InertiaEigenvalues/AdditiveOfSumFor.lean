import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachModuleUniqueness
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart

namespace GlobalTheory.WachUse

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}

theorem additive_of_sumFor (hW : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor W) : Additive W := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor at hW
  intro T T' S f g hT hT' hb hs z hz
  obtain ⟨σ, hσ, -, -, hmem⟩ := hW T T' S hT hT' f g (by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat
    exact ⟨hb, hs⟩)

  set p := σ.symm z with hp
  have hz' : σ (p.1, p.2) = z := by simp [hp]
  rw [← hz'] at hz
  obtain ⟨hx, hy⟩ := (hmem p.1 p.2).1 hz
  exact ⟨p.1, hx, p.2, hy, by rw [← hz', hσ]⟩

end Generic

theorem additive_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (C : LocCmpT l P AI H E), ∀ (K LL : FinExt l) (h : CaseA K LL),
    Additive (H.W K 1 LL h.2.2) := by
  intro l _ P _ H _ _ K LL h

  exact additive_of_sumFor (GlobalTheory.WachSum.sumPart l P H K 1 LL h.2.2)

end GlobalTheory.WachUse
