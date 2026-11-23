import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem entries_isCompact {A : Type} [TopologicalSpace A] {m n : ℕ} {C : Set A} (hC : IsCompact C) :
    IsCompact {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} := by
  have h : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have e : {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} =
      Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C)) := by
    ext M
    exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ p) q (Set.mem_univ q)⟩
  rw [e]
  exact h

theorem exists_compact_comb {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ)
    {C₁ C₂ C₃ : Set A} (h₁ : IsCompact C₁) (h₂ : IsCompact C₂) (h₃ : IsCompact C₃) :
    ∃ D : Set A, IsCompact D ∧ ∀ (x : A) (b d : Fin n → A), x ∈ C₁ → (∀ k, b k ∈ C₂) → (∀ k, d k ∈ C₃) →
      x + ∑ k, b k * d k ∈ D := by
  have hK : IsCompact (C₁ ×ˢ ((Set.pi Set.univ (fun _ : Fin n => C₂)) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => C₃)))) :=
    h₁.prod ((isCompact_univ_pi fun _ => h₂).prod (isCompact_univ_pi fun _ => h₃))
  have hc : Continuous (fun w : A × (Fin n → A) × (Fin n → A) => w.1 + ∑ k, w.2.1 k * w.2.2 k) := by
    fun_prop
  refine ⟨_, hK.image hc, fun x b d hx hb hd => ⟨(x, b, d), ⟨hx, ?_, ?_⟩, rfl⟩⟩
  · exact fun k _ => hb k
  · exact fun k _ => hd k

theorem piece_measure_lt_top : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}
    [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A)
    (_ : IsCompact C) (_ : (0 : A) ∈ C) (ν : Measure (Fx A a r × Fx A a t)) (_ : IsFiniteMeasureOnCompacts ν), ν (Piece e f P i C) < ∞ := by
  intro A _ _ _ a r t _ _ e f P i C hC h0 ν _
  obtain ⟨D₃, hD₃, h₃⟩ := exists_compact_comb (A := A) t hC hC hC
  have hS : IsCompact ((fun w : A × A => w.1 + w.2) '' (C ×ˢ C)) :=
    (hC.prod hC).image continuous_add
  obtain ⟨D, hD, hDm⟩ := exists_compact_comb (A := A) r (hC.union hD₃) hC hS
  refine lt_of_le_of_lt (measure_mono ?_)
    (((entries_isCompact (m := a) (n := r) hC).prod (entries_isCompact (m := a) (n := t) hD)).measure_lt_top)
  rintro z ⟨-, hz, hy, hv, hvi, c, hci, hc, hcv⟩
  refine ⟨hz, fun p k => ?_⟩
  have hyk : ∀ l, yc P z l k ∈ (fun w : A × A => w.1 + w.2) '' (C ×ˢ C) := fun l =>
    ⟨(f * yc P z l k, (1 - f) * yc P z l k), ⟨(hy l k).1, (hy l k).2⟩, by simp only; ring⟩
  have hvk : vc P z p k ∈ C ∪ D₃ := by
    by_cases hk : k = i
    · subst hk
      right
      have hmem := h₃ ((1 - f) * vc P z p k) c (fun j => if j = k then 0 else vc P z p j) (hvi p)
        (fun j => (hc j).2) (fun j => by
          by_cases hj : j = k
          · simpa [hj] using h0
          · simpa [hj] using hv p j hj)
      have hsum : ∑ j, c j * (if j = k then 0 else vc P z p j) = f * vc P z p k := by
        rw [hcv p]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = k
        · subst hj
          simp [hci]
        · simp [hj]
      rw [hsum] at hmem
      have hE : (1 - f) * vc P z p k + f * vc P z p k = vc P z p k := by ring
      rwa [hE] at hmem
    · exact Or.inl (hv p k hk)
  have hE : z.2 p k = vc P z p k + ∑ l, z.1 p l * yc P z l k := by
    simp [vc, Matrix.sub_apply, Matrix.mul_apply]
  rw [hE]
  exact hDm _ _ _ hvk (fun l => hz p l) hyk

end GlobalTheory.CompanionTheory.NullFr
