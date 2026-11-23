import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransportAlg
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransportAn

noncomputable section

namespace PositivityTheory.ThK

open Matrix GlobalTheory.WeilM SiegelT

theorem siegel_transport : SiegelTransport := by
  intro k _ _ _ _ _ _ K _ _ _ _ c ψ _ hq hψ _ m n N κ _ JA JB d χ Cy om _ hsk hL hW
  obtain ⟨ξ, hq⟩ := hq
  obtain ⟨hs0, dd, omd, hdd, hs, hrule, hres⟩ := hW
  obtain ⟨γ, s, s', h1, h2, hγ⟩ := exists_gamma hq.invol hsk.1 hsk.2 hL
  have hr := rule_of_conj hs γ s s' h1 h2 hγ hrule
  intro l _ hinv p t hp φ hφ
  by_cases h0 : ∀ φ ∈ SB (κ → k), l φ = 0
  · rw [h0 φ hφ, h0 _ (hs0.pres p φ hφ), mul_zero]
  push Not at h0
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  obtain ⟨gd, hgd⟩ := exists_UG (c := c) (J := dbl JB)
    (g := fromBlocks ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) 0 0 1) (by
      rw [dbl, det_fromBlocks_zero₂₁, det_neg]
      exact hsk.2.mul ((isUnit_one.neg.pow _).mul hsk.2)) (by
      have hp' : ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * JB *
        ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map c = JB := p.2
      simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one', fromBlocks_multiply]
      simp [hp'])
  let td : GL (Fin n ⊕ Fin n) K := ⟨fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 1,
    fromBlocks ((t⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0 1,
    by rw [fromBlocks_multiply, Units.mul_inv]; simp, by rw [fromBlocks_multiply, Units.inv_mul]; simp⟩
  have hdet : Matrix.GeneralLinearGroup.det td = Matrix.GeneralLinearGroup.det t :=
    Units.ext (by
      show (fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin n) (Fin n) K)).det = (t : Matrix (Fin n) (Fin n) K).det
      rw [det_fromBlocks_zero₂₁, det_one, mul_one])
  have key := hr (boxL l (conjL l)) (Set.mem_univ _) (fun z Φ hΦ => by
    have e : z * (fromBlocks Cy 0 0 Cy)ᵀ = fromCols (z.toCols₁ * Cyᵀ) (z.toCols₂ * Cyᵀ) := by
      conv_lhs => rw [← fromCols_toCols z]
      rw [fromBlocks_transpose, fromCols_mul_fromBlocks]
      simp
    rw [Darboux.rho, e, hdd]
    exact boxL_inv (norm_psi hψ) (hinv _) (hinv _) hΦ) gd td (by
      rw [hgd]
      show _ = fromBlocks Cy 0 0 Cy * fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin n) (Fin n) K)
      rw [fromBlocks_multiply, fromBlocks_multiply]
      simp [hp]) (boxFun φ (star φ₀)) (box_mem hφ (star_mem hφ₀))
  rw [hres p gd hgd φ hφ _ (star_mem hφ₀), hdet] at key
  have b : ∀ φ₁, boxL l (conjL l) (boxFun φ₁ (star φ₀)) = l φ₁ * star (l φ₀) := fun φ₁ => by
    have := boxL_box l (conjL l) φ₁ (star φ₀)
    rw [show conjL l (star φ₀) = star (l φ₀) from congrArg (fun f => star (l f)) (star_star φ₀)] at this
    exact this
  rw [b, b, ← mul_assoc] at key
  exact mul_right_cancel₀ (star_ne_zero.mpr hne) key

end PositivityTheory.ThK
