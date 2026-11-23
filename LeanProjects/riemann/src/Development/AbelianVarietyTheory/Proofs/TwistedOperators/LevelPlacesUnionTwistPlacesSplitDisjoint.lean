import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

open Classical

namespace GlobalTheory.TwistTypePlaces

private theorem isConjPl_lev_of_isConjPl_div {D : D7} {PP PP' : Pl D.host.E} (h : Formalism.L2.DIV.IsConjPl PP PP') :
    Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro c hc
  exact ⟨Formalism.DivisionValues.cO D.host.E c, (h c (Formalism.DivisionValues.cO D.host.E c) rfl).1 hc, rfl⟩

private theorem conjPl_ne_and_under_eq_of_ncard_primesOver_two {D : D7} (P : Pl D.host.E)
    (h2 : (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2) :
    Formalism.DivisionValues.conjPl P ≠ P ∧ (Formalism.DivisionValues.conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver] at h2
  have hsub : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} ⊆
      {P, Formalism.DivisionValues.conjPl P} := by
    intro u hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with hq | hq
    · exact Or.inl hq
    · exact Or.inr hq
  have hle : ({P, Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard ≤
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)}.ncard := by
    rw [h2]
    calc ({P, Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard
        ≤ ({Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hS := Set.eq_of_subset_of_ncard_le hsub hle
  refine ⟨fun hc => ?_, ?_⟩
  · rw [hS, hc, Set.pair_eq_singleton, Set.ncard_singleton] at h2
    exact absurd h2 (by decide)
  · have hmem : Formalism.DivisionValues.conjPl P ∈
        {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} := by
      rw [hS]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact hmem

theorem isSplitSet_union : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Formalism.L2.DIV.IsSplitSet (R.Pg ∪ R.Q t) ∧ Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  obtain ⟨hdisj, hinj, hcard⟩ := GlobalTheory.TwistTypePlaces.places_split R F hC t
  refine ⟨?_, hdisj⟩
  unfold Formalism.L2.DIV.IsSplitSet
  intro PP hPP PP' hPP' hc

  have hPP' : PP' = Formalism.DivisionValues.conjPl PP := GlobalTheory.GoodPrimes.isConjPl_iff.mp (isConjPl_lev_of_isConjPl_div hc)
  obtain ⟨hne, hund⟩ := conjPl_ne_and_under_eq_of_ncard_primesOver_two PP (hcard PP hPP).1
  have hsame : PP' = PP :=
    hinj (Finset.mem_coe.mpr (hPP' ▸ ‹PP' ∈ R.Pg ∪ R.Q t›)) (Finset.mem_coe.mpr hPP) (by rw [hPP']; exact hund)
  exact hne (hPP' ▸ hsame)

end GlobalTheory.TwistTypePlaces
