import Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section EqOn

variable {K : Type} [Field K] {σ : Type}

def EqOn (A : Set σ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, (↑μ.support : Set σ) ⊆ A → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G

theorem EqOn.refl (A : Set σ) (F : MvPowerSeries σ K) : EqOn A F F := fun _ _ => rfl

theorem EqOn.mul {A : Set σ} {F G F' G' : MvPowerSeries σ K} (h : EqOn A F G) (h' : EqOn A F' G') :
    EqOn A (F * F') (G * G') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hs : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have h1 : (↑p.1.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.1 ≤ μ := hs ▸ le_self_add
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  have h2 : (↑p.2.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.2 ≤ μ := hs ▸ le_add_self
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  rw [h p.1 h1, h' p.2 h2]

theorem EqOn.pow {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (k : ℕ) : EqOn A (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem EqOn.prod {A : Set σ} {ι : Type} (s : Finset ι) {F G : ι → MvPowerSeries σ K}
    (h : ∀ i ∈ s, EqOn A (F i) (G i)) : EqOn A (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem EqOn.mvExp {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) : EqOn A (mvExp F) (mvExp G) := by
  intro μ hμ
  show ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : K) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (G ^ k) / (k.factorial : K)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem EqOn.jet {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (P : MvPolynomial σ K)
    (hP : ∀ μ ∈ P.support, (↑μ.support : Set σ) ⊆ A) : jetAt0 P F = jetAt0 P G := by
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [h μ (hP μ hμ)]

theorem EqOn.rename {τ : Type} (e : σ ↪ τ) {A : Set τ} {F G : MvPowerSeries σ K}
    (h : ∀ μ : σ →₀ ℕ, (∀ x ∈ μ.support, e x ∈ A) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G) :
    EqOn A (MvPowerSeries.rename e F) (MvPowerSeries.rename e G) := by
  intro ν hν
  by_cases hr : ν ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨μ, rfl⟩ := hr
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename,
      MvPowerSeries.coeff_embDomain_rename]
    refine h μ fun x hx => hν ?_
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
    exact Finset.mem_coe.2 (Finset.mem_map_of_mem e hx)
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ hr, MvPowerSeries.coeff_rename_eq_zero _ _ hr]

end EqOn

theorem leaf_holds : LeafSt := by
  intro C _ V d _ I _ κ _ X H n Po kind hk gr
  rw [rtj_valOf]
  set A : Set (Fin n × WV I) := {x | ∃ μ ∈ Po.support, μ x ≠ 0} with hA
  refine EqOn.jet (A := A) ?_ Po fun μ hμ x hx => ⟨μ, hμ, Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx)⟩
  refine EqOn.prod _ fun ρ _ => (EqOn.refl A _).mul (EqOn.mvExp ?_)
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq]
  refine EqOn.rename (rtjR ρ) fun μ hμ => ?_
  cases hkd : kind ρ with
  | none =>
    obtain ⟨g, hg⟩ := hk.2 ρ hkd
    have h1 : ∀ w ∈ μ.support, w.1 = g := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact hg μ' hμ' w hne
    have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
      fin_cases g
      · exact Or.inl h1
      · exact Or.inr h1
    rw [H.axes μ h2]
    simp [rtjH]
  | some q =>
    obtain ⟨g, a, a'⟩ := q
    have h1 : ∀ w ∈ μ.support, X.OnLf g a a' w := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact (hk.1 ρ g a a' hkd).2.2 μ' hμ' w hne
    show MvPowerSeries.coeff μ X.hRow =
      (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0)
    rw [if_pos h1]

end Formalism.L2.FormalSeriesBounds
