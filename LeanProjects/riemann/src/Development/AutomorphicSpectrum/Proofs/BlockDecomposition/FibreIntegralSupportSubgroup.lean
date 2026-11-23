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
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

theorem smInt_zero_fun {X Z : Type} [MeasurableSpace X] [AddCommGroup Z] [Module ℂ Z]
    (μ : MeasureTheory.Measure X) (φ : X → Z) (h : ∀ x, φ x = 0) : smInt μ φ = 0 := by
  unfold smInt
  apply finsum_eq_zero_of_forall_eq_zero
  intro v
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hempty : φ ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hv (hx.symm.trans (h x))
    rw [hempty]
    simp

theorem mem_of_eq_mul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k))
    (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (h : HPG k i t) (β : Mir k (i + t)) (hβ : β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK)
    (e : uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β) :
    ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b' := by
  obtain ⟨y', _, b', hb', hβe⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_Bgrp.1 hβ
  obtain ⟨x, q, hx⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
  have e2 : uM k (i + t) y * levi k (i + t) g =
      uM k (i + t) (topV k i t x + ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y') *
        levi k (i + t) ((q : GL (Fin (i + t)) k) * b') := by
    calc uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β := e
      _ = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) *
            (uM k (i + t) y' * levi k (i + t) b') := by rw [hx, hβe]
      _ = _ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_mul_uM_levi _ _ _ _ _
  exact ⟨q, b', hb', (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_inj _ e2).2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ c K₁ hK b hb g hg
  have hz : ∀ v, fibV b g v = 0 := by
    intro v
    by_contra hne
    have hex : ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
        uM k (i + t) (midV k i t v) * levi k (i + t) g = (h : Mir k (i + t)) * β := by
      by_contra hno
      exact hne (hb _ hno)
    obtain ⟨h, β, hβ, e⟩ := hex
    exact hg (mem_of_eq_mul k i t c K₁ hK _ g h β hβ e)
  show clT τ W (smInt μ (fibV b g)) = 0
  rw [smInt_zero_fun μ _ hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

end
