import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

section Ev

variable {eps : ℝ} (Fm : FamP eps)

def Ev (P : ∀ x, Fm.x1 < x → Fm.Ix x → Prop) : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, P x hx i

variable {Fm}

theorem Ev.and {P Q : ∀ x, Fm.x1 < x → Fm.Ix x → Prop} (hP : Ev Fm P) (hQ : Ev Fm Q) :
    Ev Fm fun x hx i => P x hx i ∧ Q x hx i := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  unfold Ev
  exact ⟨max a b, fun x hx h1 i =>
    ⟨ha x (le_trans (le_max_left _ _) hx) h1 i, hb x (le_trans (le_max_right _ _) hx) h1 i⟩⟩

theorem Ev.imp {P Q : ∀ x, Fm.x1 < x → Fm.Ix x → Prop} (hP : Ev Fm P) (h : ∀ x hx i, P x hx i → Q x hx i) : Ev Fm Q := by
  obtain ⟨a, ha⟩ := hP
  unfold Ev
  exact ⟨a, fun x hx h1 i => h x h1 i (ha x hx h1 i)⟩

theorem Ev.admissible_family_of_threshold {P : ∀ x, Fm.x1 < x → Fm.Ix x → Prop} (h : ∀ x hx i, P x hx i) : Ev Fm P := by
  unfold Ev
  exact ⟨0, fun x _ hx i => h x hx i⟩

theorem Ev.of_all {P : ∀ x, Fm.Ix x → Prop} (h : ∀ x i, P x i) : Ev Fm fun x _ i => P x i := by
  unfold Ev
  exact ⟨0, fun x _ _ i => h x i⟩

theorem Ev.of_ge {P : ∀ x, Fm.Ix x → Prop} (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, P x i) : Ev Fm fun x _ i => P x i := by
  obtain ⟨a, ha⟩ := h
  unfold Ev
  exact ⟨a, fun x hx _ i => ha x hx i⟩

theorem Ev.of_le {P : ∀ x, Fm.Ix x → Prop} (h : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i, P x i) : Ev Fm fun x _ i => P x i := by
  obtain ⟨a, ha⟩ := h
  unfold Ev
  exact ⟨a, fun x hx _ i => ha x hx i⟩

theorem Ev.ge {P : ∀ x, Fm.Ix x → Prop} (h : Ev Fm fun x _ i => P x i) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, P x i := by
  obtain ⟨a, ha⟩ := h
  exact ⟨max a (Fm.x1 + 1), fun x hx i =>
    ha x (le_trans (le_max_left _ _) hx) (by linarith [le_max_right a (Fm.x1 + 1)]) i⟩

theorem Ev.le {P : ∀ x, Fm.Ix x → Prop} (h : Ev Fm fun x _ i => P x i) : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i, P x i := by
  obtain ⟨a, ha⟩ := h
  exact ⟨max a (Fm.x1 + 1), fun x hx i =>
    ha x (le_trans (le_max_left _ _) hx) (by linarith [le_max_right a (Fm.x1 + 1)]) i⟩

theorem Ev.scale (c : ℝ) : Ev Fm fun x _ i => c ≤ (Fm.L x i).sc.x := by
  unfold Ev
  exact ⟨c, fun x hx h1 i => by
    show c ≤ (Fm.L x i).sc.x
    rw [Fm.L_x x i h1]
    exact hx⟩

end Ev

theorem closed_CH_ge (𝒞 : FamClass) (c : ℝ) : Closed 𝒞 fun _ CH => c ≤ CH := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 CH (by simp [FamP.cMid])⟩⟩

theorem closed_Csz_ge (𝒞 : FamClass) (c : ℝ) : Closed 𝒞 fun Fm _ => c ≤ Fm.Csz := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 Fm.Csz (by simp [FamP.cMid])⟩⟩

theorem closed_Csz_ge_fn (𝒞 : FamClass) (c : List ℝ → ℝ) : Closed 𝒞 fun Fm _ => c Fm.cOut ≤ Fm.Csz := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 Fm.Csz (by simp [FamP.cMid])⟩⟩

end Formalism.MainNotions.DIV

end
