import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiPlaceStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HwSubStableOfComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainLengthLeFinrankAddOne
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem howe_finiteLength_uniqueMaximal_of_cyclic : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  intro T _ _ R S V _ _ a hG hc C α β α' β' hQ hAdm hCyc
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB⟩ := Places.multi_place_step T R S α β α' β'
    obtain ⟨U, hU, hUC⟩ := hAdm B
    let G : Submodule ℂ V := ⨆ (μ : ∀ w, Ix (R w) (S w) → ℚ) (_ : ∀ w c, |μ w c| ≤ B), ⨅ w, hwSub (a w) (μ w)
    have hGUC : G ≤ U ⊔ C := iSup_le fun μ => iSup_le fun h => hUC μ h
    refine ⟨Module.finrank ℂ U + 1, fun m N hN hNk => ?_⟩
    refine chain_length_le_finrank_add_one V G U C hU hGUC m N hN (fun k => (hNk k).2) ?_
    intro k l hkl
    have hQ' : ∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) (N k) (N l) := fun w c d u _ =>
      ⟨(hNk k).2 (hQ w c d u Submodule.mem_top).1, (hNk k).2 (hQ w c d u Submodule.mem_top).2⟩
    obtain ⟨μ, hμB, v, hvl, hvhw, hvk⟩ :=
      hB V a hG hc (N k) (N l) (hN hkl) (fun w => (hNk k).1 w) (fun w => (hNk l).1 w) hQ'
    refine ⟨v, hvl, ?_, hvk⟩
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    exact (le_iSup_of_le μ (le_iSup_of_le hμB le_rfl) : (⨅ w, hwSub (a w) (μ w)) ≤ G) hv
  · intro N N' hN hCN hNt hN' hCN' hN't hsup
    obtain ⟨μ, v, hvhw, hgen, hmult⟩ := hCyc
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    have hv2 : v ∈ (N ⊔ N') ⊓ ⨅ w, hwSub (a w) (μ w) := ⟨by rw [hsup]; exact Submodule.mem_top, hv⟩
    have hsp := hw_joint_split T R S V a hG hc N N' hN hN' μ hv2
    obtain ⟨n, hn, n', hn', hnn⟩ := Submodule.mem_sup.mp hsp
    obtain ⟨y, hy, c, hc', hyc⟩ := Submodule.mem_sup.mp (hmult hn.2)
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hx : x = 0
    · subst hx
      have hnC : n = c := by rw [← hyc]; simp
      have hvN' : v ∈ N' := by
        rw [← hnn]; exact N'.add_mem (hCN' (hnC ▸ hc')) hn'.1
      exact hN't (hgen N' hN' hCN' hvN')
    · have hvN : v ∈ N := by
        have h1 : x • v ∈ N := by
          have : x • v = n - c := by rw [← hyc]; simp
          rw [this]; exact N.sub_mem hn.1 (hCN hc')
        have := N.smul_mem x⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hx, one_smul] at this
      exact hNt (hgen N hN hCN hvN)

end GlobalTheory.HoweR
