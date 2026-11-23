import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

namespace GlobalTheory.FibreProj.DetPol

open Classical in

theorem pol_eq_zero_of_indep {ι : Type} [Fintype ι] (φ : (ι → ℤ) → ℝ) (i : ι)
    (h : ∀ n v, φ (Function.update n i v) = φ n) : pol φ = 0 := by
  unfold pol
  refine Finset.sum_involution (fun S _ => if i ∈ S then S.erase i else insert i S) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro S _
    have hpt : ∀ T : Finset ι, (i ∈ T ↔ i ∉ S) → (∀ j, j ≠ i → (j ∈ T ↔ j ∈ S)) →
        (fun j => if j ∈ T then (-1 : ℤ) else 0) =
          Function.update (fun j => if j ∈ S then (-1 : ℤ) else 0) i (if i ∈ T then -1 else 0) := by
      intro T _ hT
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        by_cases hS : j ∈ S
        · simp [hS, (hT j hj).2 hS]
        · have : j ∉ T := fun h' => hS ((hT j hj).1 h')
          simp [hS, this]
    by_cases hS : i ∈ S
    · simp only [hS, if_true]
      rw [hpt (S.erase i) (by simp [hS]) (fun j hj => by simp [hj]), h]
      have hc := Finset.card_erase_add_one hS
      rw [← hc, pow_succ]
      ring
    · simp only [hS, if_false]
      rw [hpt (insert i S) (by simp [hS]) (fun j hj => by simp [hj]), h]
      rw [Finset.card_insert_of_notMem hS, pow_succ]
      ring
  · intro S _ _ heq
    by_cases hS : i ∈ S
    · simp only [hS, if_true] at heq
      have hn := Finset.notMem_erase i S
      rw [heq] at hn
      exact hn hS
    · simp only [hS, if_false] at heq
      have hm := Finset.mem_insert_self i S
      rw [heq] at hm
      exact hS hm
  · intro S _
    by_cases hS : i ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

variable (α β : Type) [Fintype α] [Fintype β]

def DepOn (T : Finset β) (g : (α ⊕ β → ℤ) → ℂ) : Prop :=
  ∀ n n' : α ⊕ β → ℤ, (∀ a, n (Sum.inl a) = n' (Sum.inl a)) →
    (∀ b ∈ T, n (Sum.inr b) = n' (Sum.inr b)) → g n = g n'

def lowDeg (k : ℕ) : Submodule ℂ ((α ⊕ β → ℤ) → ℂ) :=
  Submodule.span ℂ {g | ∃ T : Finset β, T.card ≤ k ∧ DepOn α β T g}

variable {α β}

theorem mem_lowDeg_of_depOn {k : ℕ} (T : Finset β) (hT : T.card ≤ k) (g : (α ⊕ β → ℤ) → ℂ)
    (hg : DepOn α β T g) : g ∈ lowDeg α β k :=
  Submodule.subset_span ⟨T, hT, hg⟩

theorem lowDeg_mono {k l : ℕ} (h : k ≤ l) : lowDeg α β k ≤ lowDeg α β l :=
  Submodule.span_mono fun _ ⟨T, hT, hg⟩ => ⟨T, hT.trans h, hg⟩

theorem mul_mem_lowDeg {k l : ℕ} {f g : (α ⊕ β → ℤ) → ℂ} (hf : f ∈ lowDeg α β k)
    (hg : g ∈ lowDeg α β l) : f * g ∈ lowDeg α β (k + l) := by
  classical
  have gen : ∀ f, (∃ T : Finset β, T.card ≤ k ∧ DepOn α β T f) → ∀ g, g ∈ lowDeg α β l →
      f * g ∈ lowDeg α β (k + l) := by
    intro f ⟨T, hT, hfT⟩ g hg
    induction hg using Submodule.span_induction with
    | mem g hg' =>
      obtain ⟨T', hT', hgT⟩ := hg'
      refine mem_lowDeg_of_depOn (T ∪ T') ((Finset.card_union_le _ _).trans (by omega)) _ ?_
      intro n n' ha hb
      simp only [Pi.mul_apply]
      rw [hfT n n' ha (fun b hb' => hb b (Finset.mem_union_left _ hb')),
        hgT n n' ha (fun b hb' => hb b (Finset.mem_union_right _ hb'))]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  induction hf using Submodule.span_induction with
  | mem f hf' => exact gen f hf' g hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem prod_mem_lowDeg {ι : Type} (s : Finset ι) (f : ι → (α ⊕ β → ℤ) → ℂ) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ lowDeg α β (k i)) : ∏ i ∈ s, f i ∈ lowDeg α β (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact mem_lowDeg_of_depOn ∅ le_rfl _ fun _ _ _ _ => rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_lowDeg (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem pol_eq_zero_of_mem_lowDeg {k : ℕ} (hk : k < Fintype.card β) {g : (α ⊕ β → ℤ) → ℂ}
    (hg : g ∈ lowDeg α β k) : ∀ L : ℂ →ₗ[ℝ] ℝ, pol (fun n => L (g n)) = 0 := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg' =>
    obtain ⟨T, hT, hgT⟩ := hg'
    intro L
    obtain ⟨b, hb⟩ : ∃ b, b ∉ T := by
      by_contra hc
      push_neg at hc
      have := Finset.card_le_card (fun b _ => hc b : (Finset.univ : Finset β) ⊆ T)
      rw [Finset.card_univ] at this
      omega
    refine pol_eq_zero_of_indep _ (Sum.inr b) fun n v => ?_
    congr 1
    refine hgT _ _ (fun a => by simp) fun b' hb' => ?_
    have : b' ≠ b := fun h => hb (h ▸ hb')
    simp [Function.update_apply, this]
  | zero => intro L; simp [pol]
  | add x y _ _ hx hy =>
    intro L
    have h1 := hx L
    have h2 := hy L
    simp only [pol] at h1 h2 ⊢
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  | smul c x _ hx =>
    intro L
    have := hx (L ∘ₗ LinearMap.mulLeft ℝ c)
    simpa [smul_eq_mul] using this

end GlobalTheory.FibreProj.DetPol

namespace GlobalTheory.FibreProj.DetPol

theorem det_add_perturb_eq {D d : ℕ} {β : Type} [Fintype β] (A : Matrix (Fin D) (Fin D) ℂ)
    (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ) (K : β → Matrix (Fin d) (Fin d) ℂ)
    (c : β → ℂ) :
    Matrix.det (A + ∑ b, c b • (P * K b * Q)) =
      Matrix.det (Matrix.fromBlocks A (-(P * ∑ b, c b • K b)) Q 1) := by
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
  congr 2
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem pol_det_perturb_eq_zero : ∀ (D d : ℕ) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β →
    ∀ (H : α → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ)
      (K : β → Matrix (Fin d) (Fin d) ℂ),
    pol (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = 0 := by
  intro D d α β _ _ hd H P Q K
  classical
  let M : (α ⊕ β → ℤ) → Matrix (Fin D ⊕ Fin d) (Fin D ⊕ Fin d) ℂ := fun n =>
    Matrix.fromBlocks (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a)
      (-(P * ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • K b)) Q 1
  have hfun : (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) =
      fun n => Complex.reLm ((M n).det) := by
    funext n
    rw [det_add_perturb_eq]
    rfl
  rw [hfun]
  refine pol_eq_zero_of_mem_lowDeg hd ?_ Complex.reLm
  have hentry : ∀ r c : Fin D ⊕ Fin d,
      (fun n => M n r c) ∈ lowDeg α β (Sum.elim (fun _ => 0) (fun _ => 1) c) := by
    intro r c
    rcases c with j | j
    · refine mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' ha _ => ?_
      rcases r with r | r
      · simp [M, ha]
      · simp [M]
    · rcases r with r | r
      · have : (fun n => M n (Sum.inl r) (Sum.inr j)) =
            ∑ b, (-(P * K b) r j) • (fun n : α ⊕ β → ℤ => ((n (Sum.inr b) : ℝ) : ℂ)) := by
          funext n
          simp [M, Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_smul, Finset.sum_apply, mul_comm]
        rw [this]
        refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
        refine mem_lowDeg_of_depOn {b} (by simp) _ fun n n' _ hb => ?_
        simp [hb b (Finset.mem_singleton_self b)]
      · exact lowDeg_mono (Nat.zero_le 1)
          (mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' _ _ => by simp [M])
  have hdet : (fun n => (M n).det) =
      ∑ σ : Equiv.Perm (Fin D ⊕ Fin d), Equiv.Perm.sign σ • ∏ i, (fun n => M n (σ i) i) := by
    funext n
    simp [Matrix.det_apply, Finset.sum_apply, Finset.prod_apply]
  rw [show (fun n => (M n).det) = _ from hdet]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have := prod_mem_lowDeg Finset.univ (fun i => fun n => M n (σ i) i)
    (fun i => Sum.elim (fun _ => 0) (fun _ => 1) i) (fun i _ => hentry (σ i) i)
  simpa [Fintype.sum_sum_type] using this

end GlobalTheory.FibreProj.DetPol
