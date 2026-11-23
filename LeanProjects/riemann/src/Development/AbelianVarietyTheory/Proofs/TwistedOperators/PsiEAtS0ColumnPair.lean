import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridPairingBoundMemCompletionOfMapBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.HeisenbergPairBadPlaces

theorem traceCharacter_trivial_heisenbergPair_at_badPlaces : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D hQ T L μ0 hL sc G W M hM σ h h' u hu p v hv
  have hb := GlobalTheory.T.lattice_scaling_at_S0 D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) u hu v hv
  have hC := GlobalTheory.T.thetaGrid_pairingBound_mem_completion_of_mapBound G σ h h' u v hb p
  generalize hA _ _ _ = x at hC ⊢
  obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hε : GlobalTheory.FinPlLoc.idem D (· = v) ∈ idAt D (· = v) := GlobalTheory.FinPlLoc.idem_mem_idAt _
  have hs : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hε
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
    have e : GlobalTheory.SeeSaw.dI D = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA * D.host.AAbar) := by
      unfold GlobalTheory.SeeSaw.dI; rw [mul_assoc]
    rw [e, h3 _ _ hx0]
    refine ⟨?_, hs⟩
    have e1 : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    convert hC using 1
    linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * x) * e1
  have h6 := (h5 _ hs).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have e2 : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) * GlobalTheory.FinPlLoc.idem D (· = v) =
      GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) := by
    rw [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self]
  rwa [e2] at h6

end GlobalTheory.CharXFB.HeisenbergPairBadPlaces
