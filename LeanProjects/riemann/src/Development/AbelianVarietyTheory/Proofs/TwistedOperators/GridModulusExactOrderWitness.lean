import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
namespace GlobalTheory.ChiGrid.GridData

theorem modul_witness : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), ∀ v ∈ G.pl.S0,
  (∃ m ∈ G.modul, m ∉ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1)) ∧ ∃ m ∈ G.modul, m ∉ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := by
  intro D T L sc G v hv
  classical
  obtain ⟨e, he⟩ := G.pl.w_split v (Finset.mem_insert.2 (G.pl.mem_S0_of_sum_eq.1 hv))
  have hconj : Formalism.DivisionValues.conjPl (G.pl.w v) ≠ G.pl.w v := GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he

  have eqOf : ∀ (v' : HeightOneSpectrum (𝓞 D.host.F)) (Q : HeightOneSpectrum (𝓞 D.host.E)),
      (G.pl.w v').asIdeal ≤ Q.asIdeal → G.pl.w v' = Q := fun v' Q h =>
    HeightOneSpectrum.ext ((G.pl.w v').isMaximal.eq_of_le Q.isPrime.ne_top h)
  have hmod : G.modul = ∏ v' ∈ G.pl.S0, (G.pl.w v').asIdeal ^ G.pl.depth sc v' := rfl
  refine ⟨?_, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1) := fun m hm => hcon m hm
    rw [hmod, ← Finset.mul_prod_erase _ _ hv] at hle
    set J := ∏ v' ∈ G.pl.S0.erase v, (G.pl.w v').asIdeal ^ G.pl.depth sc v'
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v * (G.pl.w v).asIdeal ∣
        (G.pl.w v).asIdeal ^ G.pl.depth sc v * J := by
      rw [← pow_succ]; exact Ideal.dvd_iff_le.2 hle
    have hJ : (G.pl.w v).asIdeal ∣ J :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ (G.pl.w v).ne_bot)).1 hd
    have hJle : J ≤ (G.pl.w v).asIdeal := Ideal.le_of_dvd hJ
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (G.pl.w v).isPrime).1 hJle
    have hvv := Finset.mem_erase.1 hv'S
    have := eqOf v' (G.pl.w v) (Ideal.IsPrime.le_of_pow_le hpow)
    apply hvv.1
    rw [← G.pl.under_w hvv.2, ← G.pl.under_w hv, this]
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := fun m hm => hcon m hm
    rw [hmod] at hle
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (Formalism.DivisionValues.conjPl (G.pl.w v)).isPrime).1 hle
    have h1 := eqOf v' _ (Ideal.IsPrime.le_of_pow_le hpow)
    have h2 : v' = v := by
      rw [← G.pl.under_w hv'S, ← G.pl.under_w hv, h1, GlobalTheory.ChainTw.ParInv.under_conjPl]
    subst h2
    exact hconj h1.symm

end GlobalTheory.ChiGrid.GridData
