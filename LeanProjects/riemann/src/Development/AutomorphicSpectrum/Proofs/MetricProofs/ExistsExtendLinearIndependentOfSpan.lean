import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

namespace GlobalTheory.CompanionTheory.Ar.Exchange

theorem exists_completion_by_members (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ)
    (hw : LinearIndependent ℂ w) (hb : LinearIndependent ℂ b)
    (hwb : ∀ a, w a ∈ Submodule.span ℂ (Set.range b)) :
    ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧
      LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  classical
  let v : Fin r ⊕ Fin m → (Fin g → ℂ) := Sum.elim w b
  have hs : LinearIndepOn ℂ v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hw
  obtain ⟨B, -, hsB, hspan, hB⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let S : Finset (Fin m) := Finset.univ.filter fun j => Sum.inr j ∈ B
  let J : Fin S.card → Fin m := S.orderEmbOfFin rfl
  let φ : Fin (r + S.card) → Fin r ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ J)
  have hφ : Function.Injective φ :=
    Fin.append_injective_iff.mpr ⟨Sum.inl_injective,
      Sum.inr_injective.comp (S.orderEmbOfFin rfl).injective, fun _ _ => Sum.inl_ne_inr⟩
  have hJS : ∀ l, J l ∈ S := fun l => S.orderEmbOfFin_mem rfl l
  have hφB : Set.range φ ⊆ B := by
    rintro _ ⟨l, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp only [φ, Fin.append_left]
      exact hsB ⟨i, rfl⟩
    · simp only [φ, Fin.append_right, Function.comp_apply]
      have := hJS l
      simpa [S] using this
  have hBφ : B ⊆ Set.range φ := by
    rintro (i | j) hx
    · exact ⟨Fin.castAdd _ i, by simp [φ]⟩
    · have hj : j ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [S, hx]
      obtain ⟨l, hl⟩ := hj
      exact ⟨Fin.natAdd _ l, by simp [φ, J, hl]⟩
  have hu : LinearIndependent ℂ (v ∘ φ) := by
    rw [← linearIndepOn_range_iff hφ]
    exact hB.mono hφB
  have hle1 : Submodule.span ℂ (Set.range (v ∘ φ)) ≤ Submodule.span ℂ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show v (φ l) ∈ _
    generalize φ l = x
    rcases x with i | j
    · exact hwb i
    · exact Submodule.subset_span ⟨j, rfl⟩
  have hle2 : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (v ∘ φ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : b j ∈ Submodule.span ℂ (v '' B) := hspan ⟨Sum.inr j, Set.mem_univ _, rfl⟩
    have h2 : v '' B ⊆ Set.range (v ∘ φ) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, rfl⟩ := hBφ hx
      exact ⟨l, rfl⟩
    exact Submodule.span_mono h2 h1
  have hueq : (Fin.append w fun j => b (J j)) = v ∘ φ := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp [φ, v]
    · simp [φ, v]
  refine ⟨S.card, J, ?_, ?_⟩
  · have e1 := finrank_span_eq_card hu
    have e2 := finrank_span_eq_card hb
    rw [le_antisymm hle1 hle2, e2] at e1
    simpa using e1.symm
  · rw [hueq]
    exact hu

end GlobalTheory.CompanionTheory.Ar.Exchange
