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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedUnifAt
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
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistCond

theorem condExp_twist_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ Lc.Q t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t v τ hmu hchi hQ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hfun : chrW (GlobalTheory.SqStep.chs G i j t).ν τ =
      ((nuH G t i j).loc w).comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom) :=
    MonoidHom.ext fun x => GlobalTheory.SqStepArith.chrW_chs G hL i j t τ x
  have hloc : ∀ x, (nuH G t i j).loc w x =
      (Lc.C.mu0 j).loc w x * (Lc.xiH t).loc w x * ((G.ch.chiH (D.R.m - i)).loc w x)⁻¹ := by
    intro x
    show ((Lc.C.mu0 j * Lc.xiH t) * (G.ch.chiH (D.R.m - i))⁻¹).loc w x = _
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv]
  have h1 : GlobalTheory.SplitFlip.CondLE (unifAt v) 1 (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) := by
    rw [hfun, GlobalTheory.CondLESplit.condLE_iff]
    intro x hx hx1
    rw [hloc, hmu x hx, hchi x hx, hL.xi_tame t w x hx hx1]
    simp
  have h0 : ¬ GlobalTheory.SplitFlip.CondLE (unifAt v) 0 (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) := by
    rw [hfun, GlobalTheory.CondLESplit.condLE_iff]
    intro h
    apply (hL.Q_ram t w).2 (Or.inl hQ)
    intro x hx
    have hle : Valued.v ((x : w.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by
      simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact Valuation.map_sub_le _ (le_of_eq hx) (by simp)
    have := h x hx hle
    rw [hloc, hmu x hx, hchi x hx] at this
    simpa using this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
  have hne : ({c | GlobalTheory.SplitFlip.CondLE (unifAt v) c (chrW (GlobalTheory.SqStep.chs G i j t).ν τ)} : Set ℕ).Nonempty := ⟨1, h1⟩
  apply le_antisymm (Nat.sInf_le h1)
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have := Nat.sInf_mem hne
  rw [h] at this
  exact h0 this

end GlobalTheory.TwistCond
