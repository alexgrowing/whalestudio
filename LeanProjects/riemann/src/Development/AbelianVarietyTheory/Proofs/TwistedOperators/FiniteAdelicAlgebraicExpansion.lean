import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSplitSupportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaExpansionRationalPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedAlg

theorem moved_translate_algComb : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t x hx h hh u hu
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) := fun u v hu hv =>
    GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 _ _ u v hu hv
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.vacuum_value_algebraic_congruence hP hI hL hX t
  obtain ⟨γ, hγ, a, ha, s, hs, k, hk, hx', hkc, hss⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D A N hN x
  obtain ⟨γ', hγ', a', ha', s', hs', k', hk', hh', hkc', hss'⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D WW N hN h
  have hga : γ * a ∈ GfC A := by
    have e : γ * a = x * k⁻¹ * s⁻¹ := by rw [hx']; group
    rw [e]
    exact mul_mem (mul_mem hx (inv_mem hk)) (inv_mem hs)
  have hga' : γ' * a' ∈ GfC WW := by
    have e : γ' * a' = h * k'⁻¹ * s'⁻¹ := by rw [hh']; group
    rw [e]
    exact mul_mem (mul_mem hh (inv_mem hk')) (inv_mem hs')
  have hpair : ((x, h) : GA D A × GA D WW) = (γ * a, γ' * a') * ((s, s') * (k, k')) := by
    rw [hx', hh']
    simp only [Prod.mk_mul_mk, mul_assoc]
  obtain ⟨ζ, hζ, hkv⟩ := hlev k hk k' hk' hkc hkc'
  have h1 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (s, s') X.vac) :=
    GlobalTheory.T.weil_action_split_support hP hI hL hX t N hN s hs s' hs' hss hss'
  have h2 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t ((s, s') * (k, k')) X.vac) := by
    rw [map_mul, Module.End.mul_apply, hkv, map_smul]
    exact h1.smul hζ
  have h3 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (γ * a, γ' * a') X.vac) :=
    GlobalTheory.T.theta_expansion_rational_points hP hI hL hX t γ hγ a ha γ' hγ' a' ha' hga hga'
  have h4 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac) := by
    rw [hpair, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t _ _ h3 h2
  have h5 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) :=
    ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩
  exact om_algComb hX hψ t x h h4 h5

end GlobalTheory.MovedAlg

end
