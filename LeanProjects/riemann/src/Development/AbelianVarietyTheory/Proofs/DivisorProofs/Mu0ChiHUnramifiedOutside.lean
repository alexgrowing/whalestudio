import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistUnr

theorem mu0_chiH_unrAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ Lc.Q t → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (Lc.C.mu0 j).UnrAt w ∧ (G.ch.chiH (D.R.m - i)).UnrAt w := by
  intro D T Lc sc G μ₀ hL i j t w hw hS
  refine ⟨?_, ?_⟩
  · refine Formalism.L2.Host.IsMu0.unr (Lc.C.isMu0 j) w ?_
    intro k hmemE
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t w hw
    haveI : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    have : w.asIdeal.IsPrime := w.isPrime
    haveI : Fintype (Formalism.L2.DIV.kP w) := Fintype.ofFinite _
    have h0g : ((D.host.g k : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
      have := (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal)).2 hmemE
      simpa using this
    have h0q : ((q : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
      rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP w)
    have hd1 : ringChar (Formalism.L2.DIV.kP w) ∣ D.host.g k := ringChar.dvd h0g
    have hd2 : ringChar (Formalism.L2.DIV.kP w) ∣ q := ringChar.dvd h0q
    have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
    have h1 : ringChar (Formalism.L2.DIV.kP w) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
    exact CharP.ringChar_ne_one h1
  · have hi := i.isLt
    exact G.ch.unr (D.R.m - (i : ℕ)) (by omega) (Nat.sub_le _ _) w hS

end GlobalTheory.TwistUnr
