import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InfParts

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd.InfinitesimalSumDecomposition

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem top_zero (τ : E →+* ℂ) : HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor]

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} :
    ∀ {c : ℕ} (f : Fin c → α) (g : Fin c → β), (∀ i, R (f i) (g i)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | c + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (forall₂_ofFn _ _ fun i => h i.succ)

theorem infOf_sum (τ : E →+* ℂ) {N : ℕ} (t : Tr E N) (hg : t.Good) (hu : t.Untw) (ms : List (Multiset ℂ))
    (hms : List.Forall₂ (fun (x : Σ M : ℕ, Submodule ℂ (Sm E M)) m => HasInfCharGL x.2 τ m)
      (t.leafList.filter fun x => 0 < x.1) ms) : t.InfOf τ ms.sum := by
  induction t generalizing ms with
  | @leaf M V z =>
    have hz : z = 0 := hu z (by simp [Tr.twists])
    subst hz
    rcases hg with ⟨rfl, rfl, -⟩ | ⟨hM, -, -⟩
    · have h0 : ms = [] := by simpa [Tr.leafList] using hms
      subst h0
      exact ⟨0, top_zero τ, by simp⟩
    · have h1 : List.Forall₂ (fun (x : Σ M : ℕ, Submodule ℂ (Sm E M)) m => HasInfCharGL x.2 τ m) [⟨M, V⟩] ms := by
        simpa [Tr.leafList, hM] using hms
      rcases h1 with _ | ⟨hx, hnil⟩
      rename_i m ms'
      cases hnil
      exact ⟨m, hx, by simp⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    have hu₁ : t₁.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have hu₂ : t₂.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    simp only [Tr.leafList, List.filter_append] at hms
    have hd := List.forall₂_drop (List.filter (fun x => decide (0 < x.1)) t₁.leafList).length hms
    rw [List.drop_left] at hd
    have ht := List.forall₂_take (List.filter (fun x => decide (0 < x.1)) t₁.leafList).length hms
    rw [List.take_left] at ht
    refine ⟨_, _, ih₁ hg.1 hu₁ _ ht, ih₂ hg.2 hu₂ _ hd, ?_⟩
    rw [← List.sum_append, List.take_append_drop]

end PositivityTheory.Rg.BcB.F.LemDd.InfinitesimalSumDecomposition

namespace PositivityTheory.Rg.BcB.F.LemDd.Tw

theorem InfParts_holds : InfParts := by
  intro E _ _ _ N t P τ hg hu hp
  have h := InfinitesimalSumDecomposition.infOf_sum τ t hg hu (List.ofFn fun i => P.m i τ) (by
    unfold TreeParts at hp
    rw [← hp]
    exact InfinitesimalSumDecomposition.forall₂_ofFn _ _ fun i => P.inf i τ)
  rwa [List.sum_ofFn] at h

end PositivityTheory.Rg.BcB.F.LemDd.Tw

end
