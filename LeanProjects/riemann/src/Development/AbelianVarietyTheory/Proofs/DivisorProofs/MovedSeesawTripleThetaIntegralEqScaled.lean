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

noncomputable section

open MeasureTheory GlobalTheory.Grid

namespace GlobalTheory.BotMove

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem moveTri_ker (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → HChar D.host.E} {S : T → Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hY : Y.Is ψ θ α β νH S) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    {g : GA D A} (hg : g ∈ GfC A) (g' : GA D A') {h : GA D WW} (hh : h ∈ GfC WW) (t₀ : T) (r r' : T → ℂ)
    (t : T) (P : PolF D WW.rank A.rank) (y : GA D WW) (x : GA D A) :
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x = (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) := by
  have hgs : (ofSgn true A).symm g ∈ GfC (neg A) := hg
  have key : Y.ω t (g, h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) =
      pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t (g, h) (Y.f t)) P :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hY.weil t) hY.isVac.2.inf
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B ((ofSgn true A).symm g) h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul])
      (Y.f t) (GlobalTheory.ConstRatio.theta_f hY t).1 P).2
  show Y.ω t (x, y) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
      ((r t)⁻¹ • Y.ω t (g, h) (Y.f t)) P) 0 =
    (r t)⁻¹ * Y.ω t (x * g, y * h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) 0
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul, ← key, ← Module.End.mul_apply, ← map_mul]
  rfl

theorem moveTri_I : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g hg g' h hh t₀ r r' hr t P y
  have hk : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y = fun x => (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) :=
    funext (moveTri_ker Y ψ θ hY ΛA ΛA' ΛW hg g' hh t₀ r r' t P y)
  have he : MeasurableEmbedding (fun x : GA D A => x * g⁻¹) := (MeasurableEquiv.mulRight g⁻¹).measurableEmbedding
  have hpre : (fun x : GA D A => x * g⁻¹) ⁻¹' ((fun x => x * g) ⁻¹' Y.fd) = Y.fd := by
    ext x; simp
  have hu : IsUnit (r t)⁻¹ := isUnit_iff_ne_zero.2 (inv_ne_zero (hr t))
  constructor
  · show IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) ((fun x => x * g) ⁻¹' Y.fd)
      (Y.m.map fun x => x * g⁻¹) ↔ _
    rw [he.integrableOn_map_iff, hpre, hk]
    simp only [Function.comp_def, inv_mul_cancel_right]
    exact integrable_const_mul_iff hu _
  · show ∫ x in (fun x => x * g) ⁻¹' Y.fd, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x ∂(Y.m.map fun x => x * g⁻¹) =
      (r t)⁻¹ * ∫ x in Y.fd, Y.ker ψ θ t P (y * h) x ∂Y.m
    rw [he.setIntegral_map, hpre, hk]
    simp only [inv_mul_cancel_right]
    exact integral_const_mul _ _

end GlobalTheory.BotMove

end
