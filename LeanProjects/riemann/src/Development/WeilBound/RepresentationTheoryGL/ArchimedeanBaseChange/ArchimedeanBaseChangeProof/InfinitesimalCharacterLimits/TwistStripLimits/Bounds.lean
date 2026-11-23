import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.LengthTwistsOfStrip
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_map_add_const (m : Multiset ℂ) (w : ℂ) :
    (m.map (· + w)).sum = m.sum + (Multiset.card m : ℂ) * w := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

theorem norm_sum_le_of_le {M m : Multiset ℂ} {R : ℝ} (hle : M ≤ m) (hR : ∀ x ∈ m, ‖x‖ ≤ R) :
    ‖M.sum‖ ≤ Multiset.card M * R := by
  calc ‖M.sum‖ ≤ (M.map (fun x => ‖x‖)).sum := norm_multiset_sum_le M
    _ ≤ Multiset.card (M.map (fun x => ‖x‖)) • R := by
        refine Multiset.sum_le_card_nsmul _ _ ?_
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
        exact hR y (Multiset.subset_of_le hle hy)
    _ = Multiset.card M * R := by rw [Multiset.card_map, nsmul_eq_mul]

theorem side_bound {n : ℕ} (hn : 0 < n) (m m₁ : (E →+* ℂ) → Multiset ℂ) (w : ℂ) (R C : ℝ)
    (hcard : ∀ τ, Multiset.card (m₁ τ) = n) (hle : ∀ τ, (m₁ τ).map (· + w) ≤ m τ) (hR : ∀ τ, ∀ x ∈ m τ, ‖x‖ ≤ R)
    (hC : ‖∑ τ, (m₁ τ).sum‖ ≤ C) : ‖w‖ ≤ R + |C| ∧ ∀ τ, ∀ x ∈ m₁ τ, ‖x‖ ≤ 2 * R + |C| := by
  have hT : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos
  have h1 : ∀ τ, ‖((m₁ τ).map (· + w)).sum‖ ≤ n * R := fun τ => by
    have h := norm_sum_le_of_le (hle τ) (hR τ)
    rwa [Multiset.card_map, hcard τ] at h
  have h2 : ∑ τ, ((m₁ τ).map (· + w)).sum = ∑ τ, (m₁ τ).sum + ((Fintype.card (E →+* ℂ) * n : ℕ) : ℂ) * w := by
    simp only [sum_map_add_const, hcard, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    ring
  have h3 : ‖∑ τ, ((m₁ τ).map (· + w)).sum‖ ≤ Fintype.card (E →+* ℂ) * (n * R) := by
    calc ‖∑ τ, ((m₁ τ).map (· + w)).sum‖ ≤ ∑ τ, ‖((m₁ τ).map (· + w)).sum‖ := norm_sum_le _ _
      _ ≤ ∑ _τ : E →+* ℂ, (n * R : ℝ) := Finset.sum_le_sum fun τ _ => h1 τ
      _ = Fintype.card (E →+* ℂ) * (n * R) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hTn : (1 : ℝ) ≤ (Fintype.card (E →+* ℂ) * n : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hT.ne' hn.ne')
  have hw : ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * ‖w‖ ≤ ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * R + |C| := by
    have e : ((Fintype.card (E →+* ℂ) * n : ℕ) : ℂ) * w = ∑ τ, ((m₁ τ).map (· + w)).sum - ∑ τ, (m₁ τ).sum := by
      rw [h2]; ring
    have e2 := congrArg norm e
    rw [norm_mul, Complex.norm_natCast] at e2
    rw [e2]
    calc ‖∑ τ, ((m₁ τ).map (· + w)).sum - ∑ τ, (m₁ τ).sum‖
        ≤ ‖∑ τ, ((m₁ τ).map (· + w)).sum‖ + ‖∑ τ, (m₁ τ).sum‖ := norm_sub_le _ _
      _ ≤ Fintype.card (E →+* ℂ) * (n * R) + |C| := add_le_add h3 (hC.trans (le_abs_self C))
      _ = ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * R + |C| := by push_cast; ring
  have hwb : ‖w‖ ≤ R + |C| := by
    have hA := abs_nonneg C
    have hB : |C| ≤ ((Fintype.card (E →+* ℂ) * n : ℕ) : ℝ) * |C| := le_mul_of_one_le_left hA hTn
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_left hcon (lt_of_lt_of_le one_pos hTn)
    nlinarith
  refine ⟨hwb, fun τ x hx => ?_⟩
  have hxw : x + w ∈ m τ := Multiset.subset_of_le (hle τ) (Multiset.mem_map_of_mem _ hx)
  have hb := hR τ (x + w) hxw
  calc ‖x‖ = ‖(x + w) - w‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖x + w‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ R + (R + |C|) := add_le_add hb hwb
    _ = 2 * R + |C| := by ring

theorem block_bound {r s : ℕ} (hr : 0 < r) (hs : 0 < s) {V : Submodule ℂ (Sm E (r + s))} {V₁ : Submodule ℂ (Sm E r)}
    {V₂ : Submodule ℂ (Sm E s)} {z₁ z₂ : ℂ} {R C₁ C₂ : ℝ} (hV : IsDiscrete V) (hV₁ : IsDiscrete V₁)
    (hV₂ : IsDiscrete V₂) (hemb : Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))) (hR : InfBdd R V)
    (hC₁ : ∀ (U : Submodule ℂ (Sm E r)) (m : (E →+* ℂ) → Multiset ℂ), IsDiscrete U →
      (∀ τ, HasInfCharGL U τ (m τ)) → ‖∑ τ, (m τ).sum‖ ≤ C₁)
    (hC₂ : ∀ (U : Submodule ℂ (Sm E s)) (m : (E →+* ℂ) → Multiset ℂ), IsDiscrete U →
      (∀ τ, HasInfCharGL U τ (m τ)) → ‖∑ τ, (m τ).sum‖ ≤ C₂) :
    ‖z₁ - (s : ℂ) / 2‖ ≤ R + |C₁| ∧ ‖z₂ + (r : ℂ) / 2‖ ≤ R + |C₂| ∧
      InfBdd (2 * R + |C₁|) V₁ ∧ InfBdd (2 * R + |C₂|) V₂ := by
  have key : ∀ τ, ∃ m₁ m₂, HasInfCharGL V₁ τ m₁ ∧ HasInfCharGL V₂ τ m₂ ∧
      (m₁.map (· + (z₁ - (s : ℂ) / 2)) ≤ (hR τ).choose) ∧ (m₂.map (· + (z₂ + (r : ℂ) / 2)) ≤ (hR τ).choose) := by
    intro τ
    obtain ⟨m₁, m₂, h₁, h₂, he⟩ := infInd2_holds E r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ _ (hR τ).choose_spec.1
    refine ⟨m₁, m₂, h₁, h₂, ?_, ?_⟩
    · rw [he]; exact Multiset.le_add_right _ _
    · rw [he]; exact Multiset.le_add_left _ _
  choose m₁ m₂ h₁ h₂ hl₁ hl₂ using key
  have hRb : ∀ τ, ∀ x ∈ (hR τ).choose, ‖x‖ ≤ R := fun τ => (hR τ).choose_spec.2
  obtain ⟨a₁, b₁⟩ := side_bound hr (fun τ => (hR τ).choose) m₁ (z₁ - (s : ℂ) / 2) R C₁ (fun τ => (h₁ τ).1) hl₁ hRb
    (hC₁ V₁ m₁ hV₁ h₁)
  obtain ⟨a₂, b₂⟩ := side_bound hs (fun τ => (hR τ).choose) m₂ (z₂ + (r : ℂ) / 2) R C₂ (fun τ => (h₂ τ).1) hl₂ hRb
    (hC₂ V₂ m₂ hV₂ h₂)
  exact ⟨a₁, a₂, fun τ => ⟨m₁ τ, h₁ τ, b₁ τ⟩, fun τ => ⟨m₂ τ, h₂ τ, b₂ τ⟩⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
