import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.AlgebraicInfinityType.InfinityType

open NumberField

namespace UpperTheory.RegAlgFam

theorem exists_pairs {α : Type*} (s t : Multiset α) (h : s.card = t.card) :
    ∃ P : Multiset (α × α), P.map Prod.fst = s ∧ P.map Prod.snd = t := by
  induction s using Quotient.inductionOn with | _ l =>
  induction t using Quotient.inductionOn with | _ k =>
  have hl : l.length = k.length := by simpa using h
  refine ⟨(l.zip k : List (α × α)), ?_, ?_⟩
  · simp [List.map_fst_zip hl.le]
  · simp [List.map_snd_zip hl.ge]

theorem exists_iff {F : Type*} [Field F] [IsTotallyComplex F] {n : ℕ} (μ : (F →+* ℂ) → Multiset ℂ)
    (hc : ∀ τ, (μ τ).card = n) :
    (∃ t : Reformulated.AlgebraicInfinityType.InfinityType F n, t.IsRegularAlgebraic ∧ ∀ τ, t.exponents τ = μ τ) ↔
      ∀ τ, (μ τ).Nodup ∧ ∀ z ∈ μ τ, ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  classical
  constructor
  · rintro ⟨t, ⟨ha, hr⟩, he⟩ τ
    refine ⟨he τ ▸ hr τ, fun z hz => ?_⟩
    obtain ⟨m, hm⟩ := ha τ z (he τ ▸ hz)
    exact ⟨m, by rw [hm, add_comm]⟩
  · intro h
    choose P h1 h2 using fun τ : F →+* ℂ =>
      exists_pairs (μ τ) (μ (ComplexEmbedding.conjugate τ)) ((hc _).trans (hc _).symm)
    have cc : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    let g : (F →+* ℂ) → Prop := fun τ => (InfinitePlace.mk τ).embedding = τ
    have hg : ∀ τ, g (ComplexEmbedding.conjugate τ) ↔ ¬ g τ := by
      intro τ
      have hne : ComplexEmbedding.conjugate τ ≠ τ := fun e =>
        (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
          ⟨τ, ComplexEmbedding.isReal_iff.2 e, rfl⟩
      simp only [g, InfinitePlace.mk_conjugate_eq]
      rcases InfinitePlace.embedding_mk_eq τ with e | e
      · rw [e]; simp [hne.symm]
      · rw [e]; simp [hne]
    let Q : (F →+* ℂ) → Multiset (ℂ × ℂ) := fun τ =>
      if g τ then P τ else (P (ComplexEmbedding.conjugate τ)).map Prod.swap
    have q1 : ∀ τ, (Q τ).map Prod.fst = μ τ := by
      intro τ
      by_cases e : g τ
      · simp [Q, e, h1]
      · have := h2 (ComplexEmbedding.conjugate τ)
        rw [cc] at this
        simpa [Q, e, Multiset.map_map] using this
    have qc : ∀ τ, Q (ComplexEmbedding.conjugate τ) = (Q τ).map Prod.swap := by
      intro τ
      by_cases e : g τ
      · have e' : ¬ g (ComplexEmbedding.conjugate τ) := fun x => (hg τ).1 x e
        simp only [Q, if_pos e, if_neg e', cc]
      · simp only [Q, if_neg e, if_pos ((hg τ).2 e), Multiset.map_map]
        simp
    refine ⟨⟨Q, fun τ => by rw [← hc τ, ← q1 τ, Multiset.card_map], fun τ p hp => ?_, qc⟩,
      ⟨fun τ z hz => ?_, fun τ => ?_⟩, q1⟩
    · obtain ⟨a, ha⟩ := (h τ).2 p.1 (q1 τ ▸ Multiset.mem_map_of_mem _ hp)
      have hp' : p.2 ∈ μ (ComplexEmbedding.conjugate τ) := by
        rw [← q1, qc]
        exact Multiset.mem_map.2 ⟨p.swap, Multiset.mem_map_of_mem _ hp, rfl⟩
      obtain ⟨b, hb⟩ := (h _).2 p.2 hp'
      exact ⟨a - b, by rw [ha, hb]; push_cast; ring⟩
    · obtain ⟨m, hm⟩ := (h τ).2 z (q1 τ ▸ hz)
      exact ⟨m, by rw [hm, add_comm]⟩
    · have := (h τ).1
      rwa [← q1 τ] at this

end UpperTheory.RegAlgFam
