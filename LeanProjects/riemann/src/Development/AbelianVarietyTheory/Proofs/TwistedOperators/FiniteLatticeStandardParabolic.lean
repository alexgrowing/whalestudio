import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PieceA

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {a : Mx D m n} (ha : MxAt (fun _ => True) a) (M : Mx D n k) :
    MxAt (fun _ => True) (a ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem finLat_comap_extX {V V₀ W : HSp D} {ρ : ℕ} (d : GlobalTheory.MixModel.HypDec V V₀ ρ) {Γ : AddSubgroup (WO V W)}
    (hΓ : FinLat Γ) : FinLat (Γ.comap (d.extX W)) := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have hc : Continuous (d.extX W) := by
    show Continuous fun a : Mx D W.rank ρ => a ⬝ d.pX
    exact continuous_id.matrix_mul continuous_const
  have hinv : ∀ a : Mx D W.rank ρ, d.extX W a ⬝ d.jX = a := fun a => by
    rw [GlobalTheory.MixModel.HypDec.extX_apply, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jX, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hinv a]
    exact mxAt_mul_right (hΓ.fin _ ha) _
  · have hK : IsCompact ((fun w : WO V W => w ⬝ d.jX) '' (Γ : Set (WO V W))) :=
      hΓ.cpt.image (continuous_id.matrix_mul continuous_const)
    refine hK.of_isClosed_subset (hΓ.cpt.isClosed.preimage hc) ?_
    intro a ha
    exact ⟨_, ha, hinv a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hΓ.opn
    refine ⟨d.extX W ⁻¹' U, hU.preimage hc, by simpa using h0, fun a ha haf => ?_⟩
    exact hUA _ ha (by rw [GlobalTheory.MixModel.HypDec.extX_apply]; exact mxAt_mul_right haf _)

end GlobalTheory.AscFin.PieceA

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.PieceA

theorem finLat_pcBF_A₁ : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  have H := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at H ⊢
  delta All at H ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  exact finLat_comap_extX _ ((H D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).1

end GlobalTheory.AscFin
