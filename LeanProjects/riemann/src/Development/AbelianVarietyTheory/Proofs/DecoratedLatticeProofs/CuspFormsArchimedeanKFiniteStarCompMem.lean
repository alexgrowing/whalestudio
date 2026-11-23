import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.CuspConj

theorem isKFinite_conj {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ} (h : GlobalTheory.Doubling.IsKFinite K Φ) :
    GlobalTheory.Doubling.IsKFinite K fun g => conj (Φ g) := by
  unfold GlobalTheory.Doubling.IsKFinite GlobalTheory.Doubling.kSpan at *
  refine GlobalTheory.Mem.AutConj.finiteDimensional_span_star h ?_
  rintro f ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  funext g
  show star (conj (Φ (g * k))) = Φ (g * k)
  rw [starRingEnd_apply, star_star]

theorem conj_comp_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ u ∈ A0 θ A cA, (fun g => conj (u g)) ∈ A0 θ A cA := by
  intro D θ A cA hθ u hu
  have hu' : u ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A := hu
  show (fun g => conj (u g)) ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hu'
  obtain ⟨hs, hk⟩ := mem_autForms.1 h1
  refine Submodule.mem_inf.2 ⟨mem_autForms.2 ⟨?_, isKFinite_conj hk⟩, conj_mem_cuspCont h2⟩
  exact GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ A u hs

end GlobalTheory.Core.Rk.CuspConj

end
