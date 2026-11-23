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

open ValuativeRel Topology Uniformity GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_inv_integer_subset {W : Set k} (hW : W ∈ 𝓝 (0 : k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ x, c * x ∈ 𝒪[k] → x ∈ W := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hW
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  have hd : a * w ≠ 0 := mul_ne_zero ha0 hw0
  refine ⟨(a * w)⁻¹, inv_ne_zero hd, fun x hx => hγ ?_⟩
  have h1 : valuation k ((a * w)⁻¹ * x) ≤ 1 := hx
  have h2 : valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := by
    rw [← map_mul, mul_inv_cancel_left₀ hd]
  show valuation k x < γ
  calc valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := h2
    _ ≤ valuation k (a * w) * 1 := mul_le_mul_right h1 _
    _ = γ * valuation k w := by rw [mul_one, map_mul, ha]
    _ < γ * 1 := mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _

theorem exists_Lc_subset (t : ℕ) {W : Set (Fin t → k)} (hW : W ∈ 𝓝 (0 : Fin t → k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, o.toAdd ∈ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, s, hs, hsub⟩ := hW
  have hU : (⋂ j, s j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 hs
  obtain ⟨c, hc, h⟩ := exists_inv_integer_subset hU
  exact ⟨c, hc, fun o ho => hsub fun j _ => Set.mem_iInter.1 (h _ (ho j)) j⟩

theorem exists_Lc_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  intro k _ _ _ _ t Z _ _ φ hl hc
  letI uG : UniformSpace (Fin t → k) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (Fin t → k) := isUniformAddGroup_of_addCommGroup
  letI uZ : UniformSpace Z := ⊥
  have huc : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hmem : {p : (Fin t → k) × (Fin t → k) | φ p.1 = φ p.2} ∈ 𝓤 (Fin t → k) := by
    have h0 : {q : Z × Z | q.1 = q.2} ∈ 𝓤 Z := by
      show _ ∈ 𝓤[(⊥ : UniformSpace Z)]
      rw [bot_uniformity]
      exact Filter.mem_principal_self _
    exact huc h0
  rw [uniformity_eq_comap_nhds_zero, Filter.mem_comap] at hmem
  obtain ⟨W, hW, hsub⟩ := hmem
  obtain ⟨c, hc0, h⟩ := exists_Lc_subset t hW
  refine ⟨c, hc0, fun o ho v => ?_⟩
  have hv : (v, v + o.toAdd) ∈ (fun x : (Fin t → k) × (Fin t → k) => x.2 - x.1) ⁻¹' W := by
    show v + o.toAdd - v ∈ W
    rw [add_sub_cancel_left]
    exact h o ho
  exact (hsub hv).symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

end
