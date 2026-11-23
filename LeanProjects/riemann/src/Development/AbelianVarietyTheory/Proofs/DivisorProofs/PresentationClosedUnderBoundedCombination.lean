import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.PresSum

theorem cj_mul_of_mem (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {a b : ℂ} (ha : a ∈ M) (hb : b ∈ M) :
    StandardLatticesGL3.cj M ρ (a * b) = StandardLatticesGL3.cj M ρ a * StandardLatticesGL3.cj M ρ b := by
  unfold StandardLatticesGL3.cj TaylorLogMetric.liftM
  rw [dif_pos ha, dif_pos hb, dif_pos (mul_mem ha hb), ← map_mul]
  rfl

variable {D : D7} {T : TaylorLogMetric.Tor D} {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F₀ : TaylorLogMetric.VC D a b → ℂ}

theorem pres_zero : Pres D T L L' F₀ (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp, by
    funext z; simp [StandardLatticesGL3.comb]⟩

theorem pres_add {F G : TaylorLogMetric.VC D a b → ℂ} {n m : ℝ} (hF : Pres D T L L' F₀ F n) (hG : Pres D T L L' F₀ G m) :
    Pres D T L L' F₀ (fun z => F z + G z) (n + m) := by
  obtain ⟨k, r, y, h1, h2, h3, rfl⟩ := hF
  obtain ⟨k', r', y', h1', h2', h3', rfl⟩ := hG
  refine ⟨k + k', Fin.append r r', Fin.append y y', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h1 j
    · rw [Fin.append_right]; exact h1' j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact h2 j
    · rw [Fin.append_right]; exact h2' j
  · intro ρ
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact add_le_add (h3 ρ) (h3' ρ)
  · funext z
    simp only [StandardLatticesGL3.comb, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem pres_smul {F : TaylorLogMetric.VC D a b → ℂ} {n β : ℝ} {c : ℂ} (hβ : 0 ≤ β) (hF : Pres D T L L' F₀ F n)
    (hc : c ∈ TaylorLogMetric.Qbar) (hb : ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ c‖ ≤ β) :
    Pres D T L L' F₀ (fun z => c * F z) (β * n) := by
  obtain ⟨k, r, y, h1, h2, h3, rfl⟩ := hF
  refine ⟨k, fun i => c * r i, y, fun i => mul_mem hc (h1 i), h2, fun ρ => ?_, ?_⟩
  · simp only [fun i => cj_mul_of_mem TaylorLogMetric.Qbar ρ hc (h1 i), norm_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul (hb ρ) (h3 ρ) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hβ
  · funext z
    simp only [StandardLatticesGL3.comb, Finset.mul_sum, mul_assoc]

theorem pres_sum : ∀ (D : D7) (T : TaylorLogMetric.Tor D) (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (F₀ : TaylorLogMetric.VC D a b → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → TaylorLogMetric.VC D a b → ℂ) (n β : ℝ), 0 ≤ β → (∀ x ∈ R, Pres D T L L' F₀ (F x) n) → (∀ x ∈ R, c x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (c x)‖ ≤ β) → Pres D T L L' F₀ (fun z => ∑ x ∈ R, c x * F x z) (R.card * β * n) := by
  intro D T a b L L' F₀ α R c F n β hβ hF hc
  classical
  induction R using Finset.induction_on with
  | empty => simpa using pres_zero
  | insert x s hx ih =>
    have h1 := pres_smul hβ (hF x (Finset.mem_insert_self _ _)) (hc x (Finset.mem_insert_self _ _)).1
      (hc x (Finset.mem_insert_self _ _)).2
    have h2 := ih (fun y hy => hF y (Finset.mem_insert_of_mem hy)) (fun y hy => hc y (Finset.mem_insert_of_mem hy))
    have h3 := pres_add h1 h2
    have e : ((insert x s).card : ℝ) * β * n = β * n + s.card * β * n := by
      rw [Finset.card_insert_of_notMem hx]; push_cast; ring
    rw [e]
    simpa only [Finset.sum_insert hx] using h3

end GlobalTheory.PresSum
