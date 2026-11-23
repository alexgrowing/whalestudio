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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem colv_uM_mul_levi (n : ℕ) (y : Fin n → k) (b : GL (Fin n) k) :
    GlobalTheory.CompanionTheory.MirLevi.colv (uM k n y * levi k n b) = y := by
  have hu : ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k n y := by
    first
    | rfl
    | (ext a c; simp [GlobalTheory.CompanionTheory.BZPsiPG.uM, GlobalTheory.BZMir.unip])
  have hL : ((GlobalTheory.BZMir.levi k n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k n (b : Matrix (Fin n) (Fin n) k) := rfl
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv, Subgroup.coe_mul, Units.val_mul, hu, hL]
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem eq_uM_colv_mul_levi (n : ℕ) (p : Mir k n) :
    p = uM k n (GlobalTheory.CompanionTheory.MirLevi.colv p) * levi k n (mirabolicProjection k n p) := by
  have h1 : GlobalTheory.BZMir.mirabolicProjection k n
      (p * (GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, mul_inv_cancel]
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k n
    (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n _ h1)
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y *
      GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p) := by
    rw [← hy, inv_mul_cancel_right]
  have hy' : GlobalTheory.CompanionTheory.MirLevi.colv p = y := by
    rw [hp]
    exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi n y _
  rw [hy']
  exact hp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colv (n : ℕ) : Continuous (GlobalTheory.CompanionTheory.MirLevi.colv : Mir k n → Fin n → k) := by
  show Continuous fun p : GlobalTheory.BZMir.Mir k n => fun i : Fin n =>
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)
  first
  | exact continuous_pi fun i =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)
  | exact continuous_pi fun i => (continuous_apply (Fin.last n)).comp
      ((continuous_apply (Fin.castSucc i)).comp (Units.continuous_val.comp continuous_subtype_val))
  | fun_prop

theorem coe_Bgrp_eq (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      GlobalTheory.CompanionTheory.MirLevi.colv ⁻¹' (latt n c : Set (Fin n → k)) ∩ mirabolicProjection k n ⁻¹' (K₁ : Set (GL (Fin n) k)) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔
    (GlobalTheory.CompanionTheory.MirLevi.colv p ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c ∧ GlobalTheory.BZMir.mirabolicProjection k n p ∈ K₁)
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi]
    · rwa [map_mul, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_uM, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, one_mul]
  · rintro ⟨hy, hb⟩
    exact ⟨_, hy, _, hb, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.eq_uM_colv_mul_levi n p⟩

theorem coe_Bgrp_eq_image (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      (fun q : (Fin n → k) × GL (Fin n) k => uM k n q.1 * levi k n q.2) ''
        ((latt n c : Set (Fin n → k)) ×ˢ (K₁ : Set (GL (Fin n) k))) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔ _
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨(y, b), ⟨hy, hb⟩, rfl⟩
  · rintro ⟨⟨y, b⟩, ⟨hy, hb⟩, rfl⟩
    exact ⟨y, hy, b, hb, rfl⟩

theorem isOpen_isCompact_Bgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k))
    (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) →
    IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧
      IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  intro k _ _ _ _ n c K₁ h hK
  have hc := GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k n
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq]
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c).preimage (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.continuous_colv n)).inter
      (hK.preimage hc.2.2)
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq_image]
    have hK₁ : IsCompact (K₁ : Set (GL (Fin n) k)) :=
      (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
        (K₁.isClosed_of_isOpen hK) (SetLike.coe_subset_coe.mpr h)
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isCompact_latt n c).prod hK₁).image
      ((hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd))

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
