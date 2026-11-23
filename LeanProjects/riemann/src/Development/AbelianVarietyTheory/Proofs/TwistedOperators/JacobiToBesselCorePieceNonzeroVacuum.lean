import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.PcFBVac

variable {D : D7}

theorem mxAt_mul_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (b : Mx D k l) {a : Mx D l m} (c : Mx D m n)
    (ha : MxAt P a) : MxAt P (b * a * c) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (ha s r))

theorem pcFB_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨-, H2, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sdT : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (H2 σ h').1
  have monoB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((H2 σ h').2.1 v).1
  have monoJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((H2 (σ + 1) h).2.1 v).2
  have sdC := GlobalTheory.CosetRow.selfDual_chi hL G (2 * σ + 2) (by omega)
  have sdS : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (node_isV G hL (X := .core (2 * (σ + 1) + 1)) (show 2 * (σ + 1) + 1 ≤ D.R.m by omega)).sd
  have sdV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * (σ + 1) + 1) 0) (show 2 * (σ + 1) + 1 ≤ D.R.m ∧ 0 ≤ D.R.m by omega)).sd
  refine GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ (G.Λ (.core (2 * (σ + 1) + 1))) (lat0 F σ h') sdS sdT _ ?_
  intro u hu
  have hw := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdC.1 sdC.2 (fun _ => True) _).1 hu.1
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdS sdT]
  have hu' : u = (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0 := by
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hu']
    exact mxAt_mul_mul _ _ hw.1
  · have hj : (F.dJ (σ + 1) h).j0 *ᵥ y ∈ latV (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) fun _ => True :=
      GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace (F.dJ (σ + 1) h) sdV.1 (fun v _ => monoJ v) hy
    have h2 := hw.2 _ hj
    have e : ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) = (F.dB σ h').j0 *ᵥ (u *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    change ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) ∈ _ at h2
    rw [e] at h2
    have h3 := GlobalTheory.FinPl.ColSplitA.mulVec_mem_latA (F.dB σ h').p0
      (fun z hz => GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits _ sdT.1 (fun v _ => monoB v) hz) h2
    rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.AscFin.PcFBVac

end
