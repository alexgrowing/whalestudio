import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractRow
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem mem_iw {g : GL (Fin n) E} : g ∈ iwahori E (Fin n) ↔
    ((∀ i j, valuation E (g.val i j) ≤ 1) ∧ ∀ i j, valuation E (g⁻¹.val i j) ≤ 1) ∧
      ∀ i j, j < i → valuation E (g.val i j) < 1 := by
  rw [mem_iwahori, GlobalTheory.SplitFlip.mem_KO_iff]
  rfl

private theorem diag_one {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) (i : Fin n) :
    valuation E (g.val i i) = 1 := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  have h4 := (mem_iw.1 (inv_mem hg)).2
  refine le_antisymm (h1 i i) (not_lt.1 fun h => ?_)
  have : valuation E (∑ l, g.val i l * g⁻¹.val l i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    rw [map_mul]
    rcases lt_trichotomy l i with hl | hl | hl
    · exact (mul_le_of_le_one_right' (h2 l i)).trans_lt (h3 i l hl)
    · subst hl
      exact (mul_le_of_le_one_right' (h2 l l)).trans_lt h
    · exact (mul_le_of_le_one_left' (h1 i l)).trans_lt (h4 l i hl)
  rw [← mul_apply, g.mul_inv] at this
  simp at this

private theorem sg_mem {σ : E ≃+* E} (hσ : Isom σ) {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) :
    sg σ g ∈ iwahori E (Fin n) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  rw [mem_iw, ← map_inv]
  exact ⟨⟨fun i j => (hσ _).le.trans (h1 i j), fun i j => (hσ _).le.trans (h2 i j)⟩,
    fun i j h => (hσ _).le.trans_lt (h3 i j h)⟩

end

theorem UpperTheory.ConvolutionTheory.Loc.contractI :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E), Isom σ → ∀ t : Fin n → Eˣ, Strict t → ∀ g ∈ iwahoriCoset t,
      ∃ k ∈ iwahori E (Fin n), ∃ s ∈ torusO E (Fin n), g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
  rintro E _ _ _ _ n σ hσ t ht g ⟨a, ha, b, hb, rfl⟩
  have hb' : b * sg σ a ∈ iwahori E (Fin n) := mul_mem hb (sg_mem hσ ha)
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hb'
  have hu : uniformizer E < 1 := uniformizer_lt_one
  have ht' : ∀ j l, j < l → valuation E ((t j : E) / t l) ≤ uniformizer E := fun j l h => by
    rw [le_uniformizer_iff, map_div₀, div_lt_one₀ (zero_le.trans_lt (ht j l h))]
    exact ht j l h
  obtain ⟨k, hk, hk', s, hs, e⟩ := exists_conj hσ t le_rfl hu ht' (b * sg σ a) h1 h2 (diag_one hb')
    (diag_one (inv_mem hb')) (fun j l h => le_uniformizer_iff.2 (h3 j l h)) (fun j l h => by
      rw [map_mul]
      exact (mul_le_of_le_one_right' (h2 j l)).trans (ht' j l h))
  have hkI : k ∈ iwahori E (Fin n) := by
    refine mem_iw.2 ⟨⟨fun i j => ?_, hk'⟩, fun i j h => by simpa [one_apply_ne h.ne'] using (hk i j).trans_lt hu⟩
    rw [← sub_add_cancel (k.val i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    refine Valuation.map_add_le _ ((hk i j).trans hu.le) ?_
    rw [one_apply]
    split_ifs <;> simp
  refine ⟨k * a⁻¹, mul_mem hkI (inv_mem ha), s, inv_mem_iff.1 fun i => ?_, ?_⟩
  · have hd := diag_one (inv_mem hb') i
    show valuation E (((s i)⁻¹ : Eˣ) : E) = 1
    rw [← sub_add_cancel (((s i)⁻¹ : Eˣ) : E) ((b * sg σ a)⁻¹.val i i), Valuation.map_add_eq_of_lt_right, hd]
    exact hd ▸ (hs i).trans_lt hu
  · calc a * diagT E (Fin n) t * b = a * (diagT E (Fin n) t * (b * sg σ a)) * (sg σ a)⁻¹ := by group
      _ = _ := by rw [e, map_mul (sg σ), map_inv]; group
