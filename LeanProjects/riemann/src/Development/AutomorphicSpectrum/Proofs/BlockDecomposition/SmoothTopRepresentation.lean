import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply]
    rw [show ρ b v = v from hb]
    exact ha
  one_mem' := by
    show ρ 1 v = v
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    show ρ a⁻¹ v = v
    have ha' : ρ a v = v := ha
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem stabSub_add_le (ρ : Representation ℂ G V) (x y : V) :
    stabSub ρ x ⊓ stabSub ρ y ≤ stabSub ρ (x + y) := by
  intro g hg
  show ρ g (x + y) = x + y
  have h1 : ρ g x = x := hg.1
  have h2 : ρ g y = y := hg.2
  rw [map_add, h1, h2]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop

open GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop in
theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V), IsSmooth τ → IsSmooth (topRep τ W) := by
  intro k _ _ _ _ i V W _ _ _ _ τ hτ v
  have hU : Continuous (uMh k i) := (GlobalTheory.T.continuous_levi_unipotent_proj k i).2.1.comp continuous_toAdd
  suffices h : IsOpen (stabSub (topRep τ W) v : Set (Multiplicative (Fin i → k))) from h
  induction v using TensorProduct.induction_on with
  | zero =>
    have : (stabSub (topRep τ W) 0 : Set (Multiplicative (Fin i → k))) = Set.univ := by
      ext g
      simp only [Set.mem_univ, iff_true]
      show topRep τ W g 0 = 0
      exact map_zero _
    rw [this]
    exact isOpen_univ
  | tmul a b =>
    have hle : (stabSub τ a).comap (uMh k i) ≤ stabSub (topRep τ W) (a ⊗ₜ[ℂ] b) := by
      intro g hg
      have hg' : τ (uM k i g.toAdd) a = a := hg
      show LinearMap.rTensor W (τ (uM k i g.toAdd)) (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] b
      rw [LinearMap.rTensor_tmul, hg']
    refine Subgroup.isOpen_mono hle ?_
    exact (hτ a).preimage hU
  | add x y hx hy =>
    exact Subgroup.isOpen_mono (stabSub_add_le _ x y) (by rw [Subgroup.coe_inf]; exact hx.inter hy)
