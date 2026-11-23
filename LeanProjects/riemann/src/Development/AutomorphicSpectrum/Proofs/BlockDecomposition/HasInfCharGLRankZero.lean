import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeInfSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

inductive ListInf (τ : E →+* ℂ) : List (Σ M : ℕ, Submodule ℂ (Sm E M)) → Multiset ℂ → Prop
  | nil : ListInf τ [] 0
  | cons {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {m₀ m' : Multiset ℂ} :
      HasInfCharGL x.2 τ m₀ → ListInf τ l m' → ListInf τ (x :: l) (m₀ + m')

theorem ListInf.split (τ : E →+* ℂ) (l₁ l₂ : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (m : Multiset ℂ)
    (h : ListInf τ (l₁ ++ l₂) m) : ∃ m₁ m₂, ListInf τ l₁ m₁ ∧ ListInf τ l₂ m₂ ∧ m = m₁ + m₂ := by
  induction l₁ generalizing m with
  | nil => exact ⟨0, m, .nil, h, by simp⟩
  | cons x l ih =>
    have h' : ListInf τ (x :: (l ++ l₂)) m := h
    cases h' with
    | cons h₀ h' =>
      obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ih _ h'
      exact ⟨_, m₂, .cons h₀ h₁, h₂, by rw [add_assoc]⟩

theorem listInf_ofFn (τ : E →+* ℂ) {c : ℕ} (N : Fin c → ℕ) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (m : Fin c → Multiset ℂ) (h : ∀ i, HasInfCharGL (V i) τ (m i)) :
    ListInf τ (List.ofFn fun i => (⟨N i, V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (∑ i, m i) := by
  induction c with
  | zero => simpa using ListInf.nil
  | succ c ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    exact .cons (h 0) (ih (fun i => N i.succ) (fun i => V i.succ) (fun i => m i.succ) (fun i => h i.succ))

theorem hasInfCharGL_rank_zero (V : Submodule ℂ (Sm E 0)) (τ : E →+* ℂ) : HasInfCharGL V τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

theorem infOf_of_listInf (τ : E →+* ℂ) {N : ℕ} (t : Tr E N) (hg : t.Good) (hu : t.Untw) (m : Multiset ℂ)
    (h : ListInf τ (t.leafList.filter fun x => 0 < x.1) m) : t.InfOf τ m := by
  induction t generalizing m with
  | @leaf M V z =>
    rcases hg with ⟨rfl, rfl, rfl⟩ | ⟨hM, -, -⟩
    · have h' : ListInf τ [] m := by simpa [Tr.leafList] using h
      cases h'
      exact ⟨0, hasInfCharGL_rank_zero _ τ, by simp⟩
    · have hz : z = 0 := hu z (by simp [Tr.twists])
      subst hz
      have h' : ListInf τ [(⟨M, V⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))] m := by
        simpa [Tr.leafList, hM] using h
      cases h' with
      | cons h₀ h₁ =>
        cases h₁
        exact ⟨_, h₀, by simp⟩
  | node t₁ t₂ ih₁ ih₂ =>
    have hu₁ : t₁.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have hu₂ : t₂.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have h' := h
    simp only [Tr.leafList, List.filter_append] at h'
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ListInf.split τ _ _ m h'
    exact ⟨m₁, m₂, ih₁ hg.1 hu₁ m₁ h₁, ih₂ hg.2 hu₂ m₂ h₂, rfl⟩

theorem treeInf : PositivityTheory.Rg.BcB.F.RS.TreeInf := by
  intro hT E _ _ _ N t P τ m hg hu hp h0 hm
  have h1 := listInf_ofFn τ P.N P.V (fun i => P.m i τ) (fun i => P.inf i τ)
  have hp' : (List.ofFn fun i => (⟨P.N i, P.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      t.leafList.filter fun x => 0 < x.1 := hp
  rw [hp'] at h1
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 (hT E N t τ _ (infOf_of_listInf τ t hg hu _ h1)) hm

end GlobalTheory.CompanionTheory.TreeInfSum

end
