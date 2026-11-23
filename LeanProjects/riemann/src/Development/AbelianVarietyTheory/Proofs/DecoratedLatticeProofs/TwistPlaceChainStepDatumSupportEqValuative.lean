import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiQEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.NrmVol

theorem suppQ_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  intro D v a b r
  have hC : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE : (ValuativeRel.valuation (Fv D.host.F v)).IsEquiv
      (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hle : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z ≤ 1 ↔ Valued.v z ≤ 1 :=
    fun z => hE.le_one_iff_le_one
  have hlt : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z < 1 ↔ Valued.v z < 1 :=
    fun z => hE.lt_one_iff_lt_one
  have heq : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z = 1 ↔ Valued.v z = 1 :=
    fun z => hE.eq_one_iff_eq_one
  have htop : ∀ (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (i j : Fin r),
      topL r x i j = 0 ∨ ∃ i' j', topL r x i j = x i' j' := by
    intro x i j
    unfold topL
    split_ifs with h
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl rfl
  refine ⟨?_, ?_⟩
  · ext x
    simp only [suppQ, Set.mem_setOf_eq, GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · rintro ⟨-, hdet, hint, hlow⟩
      refine ⟨⟨fun i j => ?_, (heq _).2 hdet⟩, fun i j => (hle _).2 (hint i j),
        fun i j hi hj => (hlt _).2 (hlow i j hi hj)⟩
      rcases htop x i j with h | ⟨i', j', h⟩
      · rw [h, map_zero]; exact zero_le_one
      · rw [h]; exact (hle _).2 (hint i' j')
    · rintro ⟨⟨-, hdet⟩, hint, hlow⟩
      have hd : Valued.v (topL r x).det = 1 := (heq _).1 hdet
      refine ⟨?_, hd, fun i j => (hle _).1 (hint i j), fun i j hi hj => (hlt _).1 (hlow i j hi hj)⟩
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, map_zero] at hd
      exact zero_ne_one hd
  · ext y
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => (hle _).symm

end GlobalTheory.NrmVol
