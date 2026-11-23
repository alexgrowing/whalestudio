import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariantStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuadraticCharactersInAdjointStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEqStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepPatchTwistStatement
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IntertwinerZeroOfCharacterTwist
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IntertwinerZeroOfQuadraticTwists

open Formalism.MainNotions.N

namespace GlobalTheory.IndexTwoPatch

theorem eq_one_or_eq_of_ker {Γ : Type} [Group Γ] (η₀ η : Γ →* ℤˣ) (h : ∀ s, η₀ s = 1 → η s = 1) :
    η = 1 ∨ η = η₀ := by
  by_cases h1 : η = 1
  · exact Or.inl h1
  right
  obtain ⟨t, ht⟩ : ∃ t, η t ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact h1 (MonoidHom.ext fun x => by simpa using hc x)
  have ht' : η t = -1 := (Int.units_eq_one_or _).resolve_left ht
  have h0t : η₀ t = -1 := by
    rcases Int.units_eq_one_or (η₀ t) with h2 | h2
    · exact absurd (h t h2) ht
    · exact h2
  refine MonoidHom.ext fun s => ?_
  rcases Int.units_eq_one_or (η₀ s) with h2 | h2
  · rw [h2, h s h2]
  · have h5 : η₀ (s * t) = 1 := by
      rw [map_mul, h2, h0t]
      decide
    have h3 := h (s * t) h5
    rw [map_mul, ht'] at h3
    rw [h2]
    rcases Int.units_eq_one_or (η s) with h4 | h4
    · rw [h4] at h3
      exact absurd h3 (by decide)
    · exact h4

private theorem exists_ne_zero_smul_mem_of_mem_span' {Γ k : Type} [Group Γ] [Field k] [CharZero k] (n : ℕ)
    (ρ₀ ρj : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ) (t : Γ) (ht : η₀ t = -1)
    (h0 : IsSSRep ρ₀) (hj : IsSSRep ρj)
    (htr : ∀ g, η₀ g = 1 → η g = 1 →
      ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρj g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace)
    (hne1 : η ≠ 1) (hne2 : η ≠ η₀)
    (hB1 : ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, (ρ₀ g : Matrix (Fin n) (Fin n) k) * X = (((η g : ℤˣ) : ℤ) : k) • (X * (ρ₀ g : Matrix (Fin n) (Fin n) k))) → X = 0)
    (hB2 : ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, (ρ₀ g : Matrix (Fin n) (Fin n) k) * X = ((((η * η₀) g : ℤˣ) : ℤ) : k) • (X * (ρ₀ g : Matrix (Fin n) (Fin n) k))) → X = 0) :
    ∃ ρ : Γ →* GL (Fin n) k, (∀ g, η₀ g = 1 → ρ g = ρ₀ g) ∧ IsSSRep ρ ∧
      ∀ g, η g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρj g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.conj_on_inter_quadraticKernels_of_trace_eq Γ k n ρ₀ ρj η₀ η h0 hj htr
  have hs : ∃ s, η₀ s = 1 ∧ η s = -1 := by
    by_contra hc
    push_neg at hc
    have h4 : ∀ s, η₀ s = 1 → η s = 1 := fun s hs =>
      (Int.units_eq_one_or (η s)).resolve_right (hc s hs)
    rcases eq_one_or_eq_of_ker η₀ η h4 with h | h
    · exact hne1 h
    · exact hne2 h
  obtain ⟨s, hs0, hs1⟩ := hs
  have hY := GlobalTheory.T.intertwiner_zero_of_character_twist Γ k n ρ₀ η₀ η hB1 hB2
  obtain ⟨ρ, hρ0, hρ1⟩ := GlobalTheory.T.exists_rep_agreeing_on_kernels Γ k n ρ₀ ρj η₀ η P s hs0 hs1 hP
    (fun Y hYc => hY Y hYc s hs0)
  refine ⟨ρ, hρ0, ?_, ?_⟩
  · apply GlobalTheory.IndexTwoExt.isSSRep_of_ker η₀ t ht
    have he : ρ.comp η₀.ker.subtype = ρ₀.comp η₀.ker.subtype := by
      refine MonoidHom.ext fun x => ?_
      exact hρ0 x x.2
    rw [he]
    exact GlobalTheory.QuadKernelConj.isSSRep_ker ρ₀ η₀ h0
  · intro g hg
    rw [hρ1 g hg, Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem main : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [IsAlgClosed k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (ι : Type) [Infinite ι] (η : ι → (Γ →* ℤˣ)), Function.Injective η → (∀ i, IsOpen ((η i).ker : Set Γ)) → ∀ r : ∀ i, (η i).ker →* GL (Fin n) k, (∀ i, Continuous (r i) ∧ IsSSRep (r i)) → (∀ i (g : Γ) (h h' : (η i).ker), (h' : Γ) = g * h * g⁻¹ → ((r i h' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r i h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → (∀ i j (h : (η i).ker) (h' : (η j).ker), (h : Γ) = h' → ((r i h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r j h' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ ρ : Γ →* GL (Fin n) k, Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ j in Filter.cofinite, ∀ h : (η j).ker, ((ρ (h : Γ) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r j h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  intro Γ k _ _ _ _ _ _ _ _ n ι _ η hinj hopen r hr hconj hcomp
  have hext : ∀ i, ∃ ρ : Γ →* GL (Fin n) k, Continuous ρ ∧ IsSSRep ρ ∧ ∀ h : (η i).ker, ρ h = r i h :=
    fun i => GlobalTheory.T.exists_extension_rep_index_two_of_trace_invariant Γ k n (η i) (hopen i) (r i) (hr i).1 (hr i).2 (hconj i)
  choose ρe hρc hρs hρr using hext
  obtain ⟨i₀, hi₀⟩ : ∃ i, η i ≠ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨a, b, hab⟩ := exists_pair_ne ι
    exact hab (hinj ((hc a).trans (hc b).symm))
  obtain ⟨t, ht⟩ : ∃ t, η i₀ t = -1 := by
    by_contra hc
    push_neg at hc
    exact hi₀ (MonoidHom.ext fun x => by simpa using (Int.units_eq_one_or _).resolve_right (hc x))
  obtain ⟨B, hBdef⟩ : ∃ B : Set (Γ →* ℤˣ), B = {χ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧
      ∀ g, ((ρe i₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
        (((χ g : ℤˣ) : ℤ) : k) • (X * ((ρe i₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := ⟨_, rfl⟩
  have hB : B.Finite := by
    rw [hBdef]
    exact GlobalTheory.T.finite_quadratic_characters_in_adjoint' Γ k n (ρe i₀)
  have notB : ∀ χ : Γ →* ℤˣ, χ ∉ B → ∀ X : Matrix (Fin n) (Fin n) k,
      (∀ g, ((ρe i₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
        (((χ g : ℤˣ) : ℤ) : k) • (X * ((ρe i₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0 := by
    intro χ hχ X hX
    by_contra hX0
    rw [hBdef] at hχ
    exact hχ ⟨X, hX0, hX⟩
  have htrc : ∀ i j (g : Γ), η i g = 1 → η j g = 1 →
      ((ρe i g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace =
        ((ρe j g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
    intro i j g gi gj
    have e1 : ρe i g = r i ⟨g, gi⟩ := hρr i ⟨g, gi⟩
    have e2 : ρe j g = r j ⟨g, gj⟩ := hρr j ⟨g, gj⟩
    rw [e1, e2]
    exact hcomp i j ⟨g, gi⟩ ⟨g, gj⟩ rfl
  have hS1 : {χ : Γ →* ℤˣ | ¬ (χ ∉ B ∧ χ * η i₀ ∉ B ∧ χ ≠ 1 ∧ χ ≠ η i₀)}.Finite := by
    apply ((hB.union (Set.Finite.preimage (f := fun χ => χ * η i₀)
      (fun _ _ _ _ h => mul_right_cancel h) hB)).union (Set.toFinite {1, η i₀})).subset
    intro χ hχ
    simp only [Set.mem_setOf_eq, not_and_or, not_not] at hχ
    rcases hχ with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
  obtain ⟨j₁, hj₁⟩ := (Set.Finite.preimage (f := η) (fun _ _ _ _ h => hinj h) hS1).infinite_compl.nonempty
  have P1 : η j₁ ∉ B ∧ η j₁ * η i₀ ∉ B ∧ η j₁ ≠ 1 ∧ η j₁ ≠ η i₀ := not_not.mp hj₁
  have hS2 : {χ : Γ →* ℤˣ | ¬ ((χ ∉ B ∧ χ * η i₀ ∉ B ∧ χ ≠ 1 ∧ χ ≠ η i₀) ∧
      η j₁ * χ ∉ B ∧ η j₁ * χ * η i₀ ∉ B)}.Finite := by
    apply ((hS1.union (Set.Finite.preimage (f := fun χ => η j₁ * χ)
      (fun _ _ _ _ h => mul_left_cancel h) hB)).union (Set.Finite.preimage (f := fun χ => η j₁ * χ * η i₀)
      (fun _ _ _ _ h => mul_left_cancel (mul_right_cancel h)) hB)).subset
    intro χ hχ
    simp only [Set.mem_setOf_eq] at hχ
    by_cases h1 : (χ ∉ B ∧ χ * η i₀ ∉ B ∧ χ ≠ 1 ∧ χ ≠ η i₀)
    · by_cases h2 : η j₁ * χ ∉ B
      · have h3 : η j₁ * χ * η i₀ ∈ B := by
          by_contra h3
          exact hχ ⟨h1, h2, h3⟩
        exact Or.inr h3
      · exact Or.inl (Or.inr (not_not.mp h2))
    · exact Or.inl (Or.inl h1)
  have hev : ∀ᶠ j in Filter.cofinite, ((η j ∉ B ∧ η j * η i₀ ∉ B ∧ η j ≠ 1 ∧ η j ≠ η i₀) ∧
      η j₁ * η j ∉ B ∧ η j₁ * η j * η i₀ ∉ B) :=
    Filter.eventually_cofinite.2 (Set.Finite.preimage (f := η) (fun _ _ _ _ h => hinj h) hS2)
  obtain ⟨ρ₁, hρ1a, hρ1s, hρ1t⟩ := exists_ne_zero_smul_mem_of_mem_span' n (ρe i₀) (ρe j₁) (η i₀) (η j₁) t ht (hρs i₀) (hρs j₁)
    (fun g g0 g1 => htrc i₀ j₁ g g0 g1) P1.2.2.1 P1.2.2.2 (notB _ P1.1) (notB _ P1.2.1)
  refine ⟨ρ₁, ?_, hρ1s, ?_⟩
  · exact GlobalTheory.IndexTwoExt.continuous_of_open (η i₀).ker (hopen i₀) ρ₁ ((ρe i₀).comp (η i₀).ker.subtype)
      ((hρc i₀).comp continuous_subtype_val) (fun x => hρ1a x x.2)
  filter_upwards [hev] with j hj
  obtain ⟨ρj, hρja, hρjs, hρjt⟩ := exists_ne_zero_smul_mem_of_mem_span' n (ρe i₀) (ρe j) (η i₀) (η j) t ht (hρs i₀) (hρs j)
    (fun g g0 g1 => htrc i₀ j g g0 g1) hj.1.2.2.1 hj.1.2.2.2 (notB _ hj.1.1) (notB _ hj.1.2.1)
  have hall := GlobalTheory.T.intertwiner_zero_of_quadratic_twists Γ k n (ρe i₀) ρ₁ ρj (η i₀) (η j₁) (η j) hρ1a hρja hρ1s hρjs
    (by
      intro c hc
      apply notB
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact P1.1
      · exact hj.1.1
      · exact hj.2.1
      · exact P1.2.1
      · exact hj.1.2.1
      · exact hj.2.2)
    (by
      intro g g1 gj
      rw [hρ1t g g1, hρjt g gj]
      exact htrc j₁ j g g1 gj)
  intro h
  rw [hall h, hρjt h h.2, hρr j h]

end GlobalTheory.IndexTwoPatch
