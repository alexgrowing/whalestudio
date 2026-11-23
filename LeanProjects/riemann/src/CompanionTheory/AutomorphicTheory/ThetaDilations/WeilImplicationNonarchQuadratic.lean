import CompanionTheory.AutomorphicTheory.ThetaDilations.SqPosOfNe

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt

open CompanionTheory.PlacePermOperatorBicommutantSpan

theorem c_sb_cpt : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x :=
  fun _ _ _ _ _ _ h => ⟨fun _ hK => (co_cpt h hK).imp fun _ hL => ⟨hL.1.1, hL.1.2, hL.2⟩, fun _ hφ => by
    obtain ⟨L, L', h1, h2, h3, h4, h5⟩ := sb_level h hφ
    exact ⟨L, L', h1.1, h1.2, h2.1, h2.2, h3, h4, h5⟩⟩

theorem c_sb_span : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V, IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) → ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x :=
  fun _ _ _ _ _ _ h φ hφ L hL hinv => by
    have := h.1
    obtain ⟨s, hs⟩ := sb_span hφ hL hinv
    exact ⟨s, fun x => (congrFun hs x).trans (Finset.sum_apply _ _ _)⟩

theorem c_fou_ind : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V, fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y = ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y :=
  fun _ _ _ _ χ _ h L h1 h2 a y => by
    have := fou_ind h ⟨h1, h2⟩ a y
    have e : ind 0 (perpG h L) y = Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
      by_cases hy : y ∈ perp χ (L : Set _)
      · rw [ind_of_mem (by rw [sub_zero]; exact hy), Set.indicator_of_mem hy]
      · rw [ind_of_not (by rw [sub_zero]; exact hy), Set.indicator_of_notMem hy]
    rwa [e] at this

theorem c_fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  fun _ _ _ _ _ _ h _ hφ => fou_sb h hφ

theorem c_planch : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ :=
  fun _ _ _ _ _ _ h _ hφ => planch h hφ

theorem c_schur : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ T : (V → ℂ) → (V → ℂ), (∀ φ, SB φ → SB (T φ)) → (∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ') → (∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) → (∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u) → (∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) → ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ :=
  fun _ _ _ _ _ _ h _ _ h1 h2 h3 h4 => schur h h1 h2 h3 h4

theorem c_impl_mul : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → Impl ψ h B μ 1 id ∧ ∀ (g g' : SL(2, R)) T T', Impl ψ h B μ g T → Impl ψ h B μ g' T' → Impl ψ h B μ (g * g') (T ∘ T') :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ⟨impl_one, fun _ _ _ _ h1 h2 => impl_mul h1 h2⟩

theorem c_heis_sb : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → (∀ x y φ, SB φ → SB (Heisenberg₂ ψ h B x y φ)) ∧ (∀ b φ, SB φ → SB (opU ψ h B b φ)) ∧ ∀ (m : ℝ) (a : Rˣ) (φ : (ι → R) → ℂ), SB φ → SB (opD m (a : R) φ) :=
  fun _ _ _ _ _ _ _ _ _ _ H => ⟨fun x y _ hφ => sb_heis H x y hφ, fun b _ hφ => sb_opU H b hφ, fun m a _ hφ => sb_opD H m a hφ⟩

theorem c_impl_uniq : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (g : SL(2, R)) T T', Impl ψ h B μ g T → Impl ψ h B μ g T' → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, SB φ → T' φ = c • T φ :=
  fun _ _ _ _ _ _ _ _ _ _ H _ _ _ h1 h2 => impl_uniq H h1 h2

theorem c_impl_U : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ b : R, Impl ψ h B μ (nMat b) (opU ψ h B b) :=
  fun _ _ _ _ _ _ _ _ _ _ H b => impl_U H b

theorem c_impl_D : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (a : Rˣ) (m : ℝ), 0 < m → (∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) → Impl ψ h B μ (mMat a) (opD m (a : R)) :=
  fun _ _ _ _ _ _ _ _ _ _ H a _ hm hμ => impl_D H a hm hμ

theorem weil_implication_nonarch_quadratic : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → Impl ψ h B μ wMat (fou (chiB ψ B) μ) :=
  fun _ _ _ _ _ _ _ _ _ _ H => impl_fou_chiB H

theorem c_weil_id : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (b : Rˣ) (m : ℝ), 0 < m → (∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) → ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) = γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R) (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) :=
  fun _ _ _ _ _ _ _ _ _ _ H b _ hm hμ => weil_id H b hm hμ

end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
