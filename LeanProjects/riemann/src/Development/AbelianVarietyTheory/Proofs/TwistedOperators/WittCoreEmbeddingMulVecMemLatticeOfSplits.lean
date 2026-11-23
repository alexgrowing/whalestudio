import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.WittCoreLat

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = c ⊗ₜ[D.host.F] (M k j * z j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem i₀_mulVec_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) : ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  intro y hy
  have hX : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
  have hY : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)
  have h0 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
  refine hL _ fun v => ?_
  set c : AF D.host.F := pairA D.host.F 0 (indP D.host.F (· = v))
  refine (hmono v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have : d.pX *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pX, rat_mulVec_tmul, Matrix.mulVec_mulVec, hX, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · have : d.pY *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pY, rat_mulVec_tmul, Matrix.mulVec_mulVec, hY, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · rw [HypDec.p0, rat_mulVec_tmul, Matrix.mulVec_mulVec, h0, Matrix.one_mulVec]
    exact AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, y, hy,
      by funext k; rw [one_mul]⟩

end GlobalTheory.WittCoreLat
