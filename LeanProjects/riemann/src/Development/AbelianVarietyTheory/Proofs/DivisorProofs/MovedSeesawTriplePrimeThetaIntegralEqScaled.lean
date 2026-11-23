import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite

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

namespace GlobalTheory.BotMove

open MeasureTheory

theorem int_prime_moveTri : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g g' hg' h hh t₀ r r' hr' t P y
  have hW : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hY.weil' t
  have hθ : IsInfFam θ := hY.isVac'.2.inf
  have hf := (GlobalTheory.ConstRatio.theta_f hY t).2
  have hk : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g') := by
    intro x
    change thetaKO (Y.ω' t) x y (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
      ((r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)) P) = (r' t)⁻¹ * thetaKO (Y.ω' t) (x * g') (y * h)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)
    rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW _ _ (Y.ω' t) hW hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B g' h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hf P).2]
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  let e : GA D A' ≃ᵐ GA D A' := MeasurableEquiv.mulRight g'⁻¹
  have hm : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = Y.m'.map e := rfl
  have hs : e ⁻¹' (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd' = Y.fd' := by
    ext x
    change x * g'⁻¹ * g' ∈ Y.fd' ↔ x ∈ Y.fd'
    rw [inv_mul_cancel_right]
  have hc : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x) = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) x := by
    intro x
    rw [hk]
    change (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g'⁻¹ * g') = _
    rw [inv_mul_cancel_right]
  have hu : IsUnit (r' t)⁻¹ := IsUnit.mk0 _ (inv_ne_zero (hr' t))
  constructor
  · rw [hm, integrableOn_map_equiv, hs]
    change Integrable (fun x => (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x)) (Y.m'.restrict Y.fd') ↔ _
    simp_rw [hc]
    exact integrable_const_mul_iff hu _
  · change ∫ x in (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd', (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x
        ∂(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = (r' t)⁻¹ * ∫ x in Y.fd', Y.ker' ψ θ t P (y * h) x ∂Y.m'
    rw [hm, setIntegral_map_equiv, hs]
    simp_rw [hc]
    exact integral_const_mul _ _

end GlobalTheory.BotMove
