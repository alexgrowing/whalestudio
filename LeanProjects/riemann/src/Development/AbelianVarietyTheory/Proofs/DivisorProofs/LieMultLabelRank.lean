import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

theorem exists_open_psiAway_mem_conj_level : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : G.C) (r₁ : G.GAf),
    letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C);
    ∃ O : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, InT G (AfP p) β y z →
      ∃ k ∈ L.K.toSubgroup, ((r₁ * k * r₁⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x z := by
  intro p _ G L β x t hx y r₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  let K' : Set G.GAf := (fun g : G.GAf => r₁⁻¹ * g * r₁) ⁻¹' (L.K : Set G.GAf)
  have hK'o : IsOpen K' :=
    L.K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hK'o
  refine ⟨psiAway G x ⁻¹' V, hVo.preimage ?_, ?_, ?_⟩
  · show Continuous (fun z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ => ((x * z.1 * x⁻¹, z.2) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ))
    exact ((continuous_const.mul continuous_fst).mul continuous_const).prodMk continuous_snd
  · have h1 : (1 : G.GAf) ∈ K' := by
      show r₁⁻¹ * 1 * r₁ ∈ (L.K : Set G.GAf)
      rw [mul_one, inv_mul_cancel]
      exact L.K.one_mem
    rw [← hV] at h1
    show psiAway G x 1 ∈ V
    rw [map_one]
    exact h1
  · intro z hz hT
    have hw : psiAway G x z ∈ UPts G.star (AfP p) := by
      rw [psiAway_apply]
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) (β : G.C)) x z.1 t (z.2 : AfP p) hx hT.1
    let g : G.GAf := ⟨psiAway G x z, hw⟩
    have hg : g ∈ K' := by
      rw [← hV]
      exact hz
    refine ⟨r₁⁻¹ * g * r₁, hg, ?_⟩
    have : r₁ * (r₁⁻¹ * g * r₁) * r₁⁻¹ = g := by group
    rw [this]

end GlobalTheory.TorCls
