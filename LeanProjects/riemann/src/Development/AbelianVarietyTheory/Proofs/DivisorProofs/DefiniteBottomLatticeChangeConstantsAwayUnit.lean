import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValidStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTupleStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.SqTower

theorem bottom_lattices : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW X Y hX hY
  have hYi := hY.2.2.2.2.2.2.2
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.FinPl.BasePoint.exists_base A Y.rA.Λ X.rA.Λ hYi.rigA.1 hX.is.rigA.1
  obtain ⟨g', hg', hgm'⟩ := GlobalTheory.FinPl.BasePoint.exists_base A' Y.rA'.Λ X.rA'.Λ hYi.rigA'.1 hX.is.rigA'.1
  obtain ⟨h, hh, hhm⟩ := GlobalTheory.FinPl.BasePoint.exists_base WW Y.rW.Λ X.rW.Λ hYi.rigW.1 hX.is.rigW.1
  obtain ⟨r, r', hr0, hr, hr', hζ⟩ := GlobalTheory.T.moved_vacua_scalar_multiples_reference_tuple μ₀ hL W S hN i j Y hY g hg g' hg' h hh
  have hZi := GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ hX.is.rigA.1 hX.is.rigA'.1 hX.is.rigW.1 g hg g' hg' h hh
    (hgm _) (hgm' _) (hhm _) μ₀ r r' hr0 hr hr'
  have hI := GlobalTheory.T.movedSeesawTriple_thetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g hg g' h hh μ₀ r r' (fun t => (hr0 t).1)
  have hI' := GlobalTheory.T.movedSeesawTriple_primeThetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g g' hg' h hh μ₀ r r' (fun t => (hr0 t).2)
  refine ⟨moveTri Y X.rA.Λ X.rA'.Λ X.rW.Λ g g' h μ₀ r r', fun t => r' t / r t,
    ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1, hY.2.2.2.2.1, hY.2.2.2.2.2.1, hY.2.2.2.2.2.2.1, hZi⟩,
    rfl, rfl, rfl, fun t => ⟨div_ne_zero (hr0 t).2 (hr0 t).1, hζ t⟩, ?_⟩
  rintro c ⟨⟨t₁, ht₁⟩, P, P', hc⟩
  refine ⟨⟨t₁, mul_ne_zero (div_ne_zero (hr0 t₁).2 (hr0 t₁).1) ht₁⟩, P, P', fun t =>
    ⟨fun y => ⟨(hI t P y).1.2 ((hc t).1 (y * h)).1, (hI' t P' y).1.2 ((hc t).1 (y * h)).2⟩, ?_, fun y => ?_⟩⟩
  · obtain ⟨y₀, hy₀⟩ := (hc t).2.1
    refine ⟨y₀ * h⁻¹, ?_⟩
    rw [(hI' t P' _).2, inv_mul_cancel_right]
    exact mul_ne_zero (inv_ne_zero (hr0 t).2) hy₀
  · rw [(hI t P y).2, (hI' t P' y).2, (hc t).2.2 (y * h)]
    field_simp [(hr0 t).1, (hr0 t).2]

end GlobalTheory.SqTower
