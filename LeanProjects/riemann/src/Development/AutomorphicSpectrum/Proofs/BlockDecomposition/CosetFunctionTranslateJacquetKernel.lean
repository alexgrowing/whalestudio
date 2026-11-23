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

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem topPart_append_zero (i t : ℕ) (a : Fin t → k) : topP i t (Fin.append (0 : Fin i → k) a) = 0 := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_append_zero (i t : ℕ) (a : Fin t → k) : middlePart i t (Fin.append (0 : Fin i → k) a) = a := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_cosetFn_translate (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) :
    fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z) = cosetFn t hc 0 z := by
  apply Subtype.ext
  funext v
  have h1 : Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)) = 1 :=
    congrArg Multiplicative.ofAdd (topPart_append_zero i t a)
  have h2 : (fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z)).1 v
      = ρ₀ (Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)))
        ((cosetFn t hc a z).1 (v + middlePart i t (Fin.append (0 : Fin i → k) a))) := rfl
  rw [h2, h1, map_one, middlePart_append_zero]
  show (cosetSet t c a).indicator (fun _ => z) (v + a) = (cosetSet t c 0).indicator (fun _ => z) v
  have hs : (v + a ∈ cosetSet t c a) ↔ v ∈ cosetSet t c 0 := by
    have : v + a - a = v - 0 := by simp
    show Multiplicative.ofAdd (v + a - a) ∈ Lc t c ↔ Multiplicative.ofAdd (v - 0) ∈ Lc t c
    rw [this]
  classical
  by_cases hv : v ∈ cosetSet t c 0
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hs.2 hv)]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv (hs.1 h))]

theorem cosetFn_sub_cosetFn_zero_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  intro k _ _ _ _ i t Z _ _ ρ₀ c hc a z
  have hgen : cosetFn t hc 0 z - cosetFn t hc a z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩, cosetFn t hc a z, ?_⟩
    have h1 : (((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ)
        ⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩ : ℂˣ) : ℂ) = 1 := rfl
    rw [h1, one_smul]
    exact congrArg (· - cosetFn t hc a z) (fibAct_cosetFn_translate i t ρ₀ hc a z).symm
  have := Submodule.neg_mem _ hgen
  rwa [neg_sub] at this

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
