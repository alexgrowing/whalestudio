import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut

noncomputable section

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.BcB.F.ChiPin

open PositivityTheory.Rg.BcB.F

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem chi_pin (gen : Γ → Prod' H d) (a₀ : Γ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (ha₀ : (gen a₀).2 v = v)
    (s : ι) (X : H s →L[ℂ] H s)
    (χ : StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})
      →⋆ₐ[ℂ] ℂ)
    (heig : ∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c)
    (a : StarAlgebra.adjoin ℂ (Set.range gen)) (c : ℂ) (hc : a.1.2 v = c • v) :
    χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c := by
  have key : ∀ b : StarAlgebra.adjoin ℂ (Set.range gen), ∀ e : ℂ, e ≠ 0 → b.1.2 v = e • v →
      χ ⟨b.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨b, rfl⟩)⟩ = e := by
    intro b e he hb
    obtain ⟨c', hc', hχ⟩ := heig b (by rw [hb]; exact smul_ne_zero he hv)
    rw [hχ]
    have h2 : (c' - e) • v = 0 := by rw [sub_smul, ← hc', ← hb, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv)
  by_cases h0 : c = 0
  · subst h0
    let g : StarAlgebra.adjoin ℂ (Set.range gen) := ⟨gen a₀, StarAlgebra.subset_adjoin ℂ _ ⟨a₀, rfl⟩⟩
    have hg : g.1.2 v = (1 : ℂ) • v := by rw [one_smul]; exact ha₀
    have hab : (a + g).1.2 v = (1 : ℂ) • v := by
      change (a.1.2 + g.1.2) v = _
      rw [ContinuousLinearMap.add_apply, hc, hg, zero_smul, zero_add]
    have e1 := key (a + g) 1 one_ne_zero hab
    have e2 := key g 1 one_ne_zero hg
    have hsum : (⟨(a + g).1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a + g, rfl⟩)⟩ :
        StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})) =
        ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ +
          ⟨g.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ := rfl
    rw [hsum, show ∀ p q, χ (p + q) = χ p + χ q from fun p q => χ.toAlgHom.map_add p q, e2] at e1
    linear_combination e1
  · exact key a c h0 hc

end PositivityTheory.Rg.BcB.F.ChiPin

end
