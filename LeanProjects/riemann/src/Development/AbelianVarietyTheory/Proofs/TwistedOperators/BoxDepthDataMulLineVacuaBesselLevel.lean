import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentEqKappaLatticePointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BoxBF

theorem isHalf_mul {D : D7} {m n k : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (M : Mx D n k) : IsHalf e (u ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ →
    VacG W.ψ _ _ (lineLat F ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ (pcBF W F ρ h).Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h Ξ₁ Ξ₂ h1 h2 h3
  have hn : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  refine ⟨(F.oB ρ h).isThetaFunO_boxS h1.1 h2, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    rw [OrthDec.heisO_boxS, map_nsmul, Prod.smul_fst, Prod.smul_snd,
      h1.2.1 _ (GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu), hw',
      (GlobalTheory.T.linked_line_hom_transport_lattice_vacua D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).1]
  · intro e he u hu hh
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    have ha : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 := isHalf_mul hh _
    have hb : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 := isHalf_mul hh _
    rw [OrthDec.heisO_boxS, h1.2.2 e he _ (GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu) ha, hw']
    rw [hw'] at hb
    rw [(GlobalTheory.T.linked_line_hom_transport_lattice_vacua D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).2 e he hb]

end GlobalTheory.AscFin.BoxBF
