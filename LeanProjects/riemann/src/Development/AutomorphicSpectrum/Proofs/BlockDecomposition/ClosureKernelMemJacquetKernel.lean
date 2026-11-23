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

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem tmul_mem_twKer_topRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) {w : V} (hw : w ∈ twKer τ (MirUin k i) 1) (b : W) :
    w ⊗ₜ[ℂ] b ∈ twKer (topRep τ W) ⊤ 1 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, a, rfl⟩ := hw
    obtain ⟨x, hx⟩ := exists_uM_of_mem k i n.2
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩, a ⊗ₜ[ℂ] b, ?_⟩
    have h1 : topRep τ W (Multiplicative.ofAdd x) (a ⊗ₜ[ℂ] b) = (τ (uM k i x) a) ⊗ₜ[ℂ] b := rfl
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [h1, hx, TensorProduct.sub_tmul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [TensorProduct.add_tmul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c hx

theorem mem_twKer_topRep_of_clT_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  intro k _ _ _ _ i V W _ _ _ _ τ z hz
  have hex : Function.Exact (twKer τ (MirUin k i) 1).subtype (twKer τ (MirUin k i) 1).mkQ :=
    LinearMap.exact_subtype_mkQ _
  obtain ⟨y, rfl⟩ := (rTensor_exact W hex (Submodule.mkQ_surjective _) z).1 hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => exact tmul_mem_twKer_topRep k i τ w.2 b
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
