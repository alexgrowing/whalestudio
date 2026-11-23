import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.UnitPos

theorem norm_twG_le {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.W v) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y)‖ ≤ 1 := by
  have h := E.compat v s.val y
  have e : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y) =
      E.iK (X.G.P.ι v ((X.G.P.σ v ^ s.val) (algebraMap (X.G.P.W v) (X.G.P.Qq v) y))) := rfl
  rw [e, h, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
  exact Formalism.L2.G.Pend.norm_wToC_le p _

theorem norm_twG_unit {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : (X.G.P.W v)ˣ) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_le X E v s (y : X.G.P.W v)
  have h2 := norm_twG_le X E v s ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have hm : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v)) *
      twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hn := congrArg norm hm
  rw [norm_mul, norm_one] at hn
  have h0 : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ := norm_nonneg _
  have h0' : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))‖ := norm_nonneg _
  nlinarith

end GlobalTheory.TwV.UnitPos

namespace GlobalTheory.TwV.UnitPos

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom

end GlobalTheory.TwV.UnitPos

open GlobalTheory.TwV.UnitPos in

theorem GlobalTheory.TwV.UnitPos.norm_embT_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι b hb hloc τ
  obtain ⟨⟨v, s⟩, rfl⟩ := (hT.gat_pos u w hg).surjective τ
  have hq := embT_mem_qbar D ((hT.gat_pos u w hg) ⟨v, s⟩) b
  have e1 : ι (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) := by
    rw [TaylorLogMetric.lamC, dif_pos hq]
    exact hι ⟨_, hq⟩
  rw [e1, hS v s b]
  obtain ⟨y, hy⟩ := hloc v
  split_ifs with ho
  · have hc : J.rho std v (D.host.conj b) = algebraMap _ _ (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) := by
      have h1 : J.rho std v (D.host.conj b) * J.rho std v b = 1 := by
        rw [← map_mul, mul_comm, hb, map_one]
      have h2 : algebraMap ((sysS H X std).G.P.W v) ((sysS H X std).G.P.Qq v) (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) *
          J.rho std v b = 1 := by
        rw [hy, ← map_mul, Units.inv_mul, map_one]
      have hne : J.rho std v b ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    rw [hc]
    exact norm_twG_unit _ S.E v s _
  · rw [hy]
    exact norm_twG_unit _ S.E v s y
