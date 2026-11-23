import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

variable {D : D7}

theorem symplO_half_off (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x) (hu : ∀ i j, cA D a * u i j = 0) :
    symplO S T x u = 0 := by
  have h0 : cA D a • u = 0 := Matrix.ext fun i j => by
    show cA D a * u i j = 0
    exact hu i j
  rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx, GlobalTheory.SplitScalar.symplO_smul, h0, GlobalTheory.SplitScalar.symplO_zero_right]

theorem heisO_comm_off (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x)
    (hu : ∀ i j, cA D a * u i j = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_skew, symplO_half_off S T hx hu, neg_zero,
    AddChar.map_zero_eq_one, one_smul]

theorem heisO_fix_thetaAt_off : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T))
    (c : ℂ) (f₀ Φ f : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → ∀ u : WO S T,
    (∀ i j, e * u i j = 0 ∧ cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f h u hu hf₀
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  have hm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((GlobalTheory.SplitScalar.heisL ψ S T u).comp Tm) :=
    { trans := fun Φ' hΦ' x hx => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.trans Φ' hΦ' x hx, heisO_comm_off ψ S T hx (fun i j => (hu i j).2)]
      modul := fun Φ' hΦ' y hy => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.modul Φ' hΦ' y hy,
          heisO_comm_off ψ S T hy (fun i j => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (hu i j).1)]
      vac := by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.vac, hf₀] }
  have h1 := hall _ hm
  have h2 := hall _ hTm
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at h1
  rw [h2] at h1 ⊢
  exact h1.symm

end GlobalTheory.Hk3

end
