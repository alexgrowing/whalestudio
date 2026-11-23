import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem polDense : PositivityTheory.ThKG.PolDense := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have h0 := fun T hT => Dense.pol_dense M hP.base hP.herm hP.skew T hT
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hnd
  obtain ⟨x, hx⟩ : ∃ x, x ∉ (M.Pol B.ψ B.emb).topologicalClosure := by
    by_contra h
    push Not at h
    exact hnd (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, u, hfs, hfx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (((M.Pol B.ψ B.emb).topologicalClosure.restrictScalars ℝ).convex)
    (M.Pol B.ψ B.emb).isClosed_topologicalClosure hx
  have hf0 : ∀ a ∈ (M.Pol B.ψ B.emb).topologicalClosure, f a = 0 := by
    intro a ha
    by_contra hne
    have hmem : ((((|u| + 1 : ℝ) : ℂ) / f a) • a) ∈ (M.Pol B.ψ B.emb).topologicalClosure :=
      (M.Pol B.ψ B.emb).topologicalClosure.smul_mem _ ha
    have hlt := hfs _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hlt
    simp at hlt <;> linarith [le_abs_self u]
  have hfz : f = 0 := h0 f (fun g hg => hf0 g ((M.Pol B.ψ B.emb).le_topologicalClosure hg))
  have h00 := hfs 0 (Submodule.zero_mem _)
  rw [hfz] at hfx
  simp at hfx h00
  linarith

end GlobalTheory.ThK.Dbl

end
