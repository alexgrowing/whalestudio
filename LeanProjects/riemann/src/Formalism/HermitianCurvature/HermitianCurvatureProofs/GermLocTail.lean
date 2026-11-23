import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem GermD.germLoc_tail (hG : GermD s β ε Y ut bt SS) (Gk : ι × ℂ → ι × ℂ → ℂ)
    (hGk : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Gk (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x'))
    (hatB : ℂ → ι → ι → ℂ) (hN : ∀ σ : ℂ, ∀ h ∈ Y, ∀ h' ∈ Y, Nhat s β bt σ h h' = hatB σ h h') :
    (∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z => ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ)) ∧
    ∃ Pua Paa : ι × ℂ → ι × ℂ → ℂ,
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) Gk Pua Paa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖Paa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
        Tendsto (fun x => Paa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => Pua (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hatB σ h h')) ∧
        Tendsto (fun x => conj (Pua (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hatB σ h h')) := by
  obtain ⟨h0, h1, h2, h3⟩ := hG.propG
  refine ⟨fun h hh h' hh' => integrable_inner_of_memLp (h0 h hh).1 (h0 h' hh').1,
    gramL volume (Uc s ut) (Ac s β ε bt), gramL volume (Ac s β ε bt) (Ac s β ε bt),
    fun Xs hXs => ?_, h2, fun h hh h' hh' σ => ?_⟩
  · have hb := h1 Xs hXs
    unfold KB.BlockPSD TB.PSDOn at hb ⊢
    open scoped ComplexOrder in
    refine (congrArg Matrix.PosSemidef ?_).mpr hb
    ext i j
    obtain ⟨x, hx⟩ := i
    obtain ⟨y, hy⟩ := j
    rcases x with p | q <;> rcases y with p' | q'
    · have hp := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hx)
      have hp' := Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hy)
      show Gk p p' = gramL volume (Uc s ut) (Uc s ut) p p'
      exact hGk p.1 hp.1 p'.1 hp'.1 p.2 p'.2 (hXs _ hp.2) (hXs _ hp'.2)
    · rfl
    · rfl
    · rfl
  · rw [← hN σ h hh h' hh']
    exact h3 h hh h' hh' σ

end

end Formalism.FourierDecayAlt.P.PBK
