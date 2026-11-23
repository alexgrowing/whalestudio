import Mathlib
import Formalism.HermitianCurvature.StatementTB

namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data

open scoped ComplexOrder

noncomputable section

open Classical

theorem sqrt_form_sum_le {n ι : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (I : Finset ι) (x : ι → n → ℂ) :
    √(((M *ᵥ (∑ s ∈ I, x s)) ⬝ᵥ star (∑ s ∈ I, x s)).re) ≤
      ∑ s ∈ I, √(((M *ᵥ x s) ⬝ᵥ star (x s)).re) :=
  @norm_sum_le _ _ (M.toSeminormedAddCommGroup hM) I x

def ind {α : Type} (Y A : Finset α) : Y → ℂ := fun p => if (p : α) ∈ A then 1 else 0

theorem sum_mul_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (g : α → ℂ) :
    ∑ q : Y, g q * ind Y A q = ∑ q ∈ A, g q := by
  have h := Finset.sum_coe_sort Y (fun q => g q * (if q ∈ A then (1 : ℂ) else 0))
  simp only [ind]
  rw [h]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA]

theorem star_ind {α : Type} (Y A : Finset α) : star (ind Y A) = ind Y A := by
  funext p
  simp only [Pi.star_apply, ind]
  split_ifs <;> simp

theorem form_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (k : α → α → ℂ) :
    ((Matrix.of fun x y : Y => k x y) *ᵥ ind Y A) ⬝ᵥ star (ind Y A) = ∑ p ∈ A, ∑ q ∈ A, k p q := by
  rw [star_ind]
  simp only [dotProduct, mulVec, of_apply]
  have h1 : ∀ p : Y, ∑ q : Y, k p q * ind Y A q = ∑ q ∈ A, k p q :=
    fun p => sum_mul_ind Y A hA (fun q => k p q)
  simp only [h1]
  exact sum_mul_ind Y A hA (fun p => ∑ q ∈ A, k p q)

theorem psd_mul {α : Type} {Y : Finset α} {k₁ k₂ : α → α → ℂ} (h₁ : PSDOn Y k₁) (h₂ : PSDOn Y k₂) :
    PSDOn Y (fun p q => k₁ p q * k₂ p q) :=
  Matrix.PosSemidef.hadamard h₁ h₂

theorem psd_pull {α β : Type} {Y : Finset α} (g : α → β) {k : β → β → ℂ}
    (h : PSDOn (Y.image g) k) : PSDOn Y (fun p q => k (g p) (g q)) :=
  Matrix.PosSemidef.submatrix h (fun p : Y => (⟨g p, Finset.mem_image_of_mem g p.2⟩ : Y.image g))

theorem psd_sum_nonneg {α : Type} {Y : Finset α} {k : α → α → ℂ} (h : PSDOn Y k) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q).re := by
  rw [← form_ind Y Y (Finset.Subset.refl Y) k, dotProduct_comm]
  exact Matrix.PosSemidef.re_dotProduct_nonneg h _

variable {E W : Type} [Field E]

theorem last_size (T : Tower E) {i : ℕ} (hi : 1 ≤ i) {p : Pt E} (hp : p ∈ T.X i) :
    ∃ s ∈ Icc 1 i, p.getLast?.map Prod.fst = some s := by
  obtain ⟨hl, hb⟩ := (T.isTower i p).1 hp
  rcases List.eq_nil_or_concat p with rfl | ⟨h, b, rfl⟩
  · simp [level] at hl; omega
  · refine ⟨b.1, ?_, by simp⟩
    have h1 : 1 ≤ b.1 := by simpa using (hb h.length (by simp)).1
    have h2 : level (h.concat b) = level h + b.1 := by simp [level]
    rw [Finset.mem_Icc]
    exact ⟨h1, by omega⟩

theorem sum_ind_Xs (T : Tower E) {i : ℕ} (hi : 1 ≤ i) :
    ∑ s ∈ Icc 1 i, ind (T.X i) (Xs T i s) = ind (T.X i) (T.X i) := by
  funext p
  obtain ⟨s, hs, hps⟩ := last_size T hi p.2
  rw [Finset.sum_apply, Finset.sum_eq_single s]
  · have hm : (p : Pt E) ∈ Xs T i s := by
      simp only [Xs, Finset.mem_filter]
      exact ⟨p.2, hps⟩
    simp [ind, hm]
  · intro s' _ hne
    have : (p : Pt E) ∉ Xs T i s' := by
      simp only [Xs, Finset.mem_filter, not_and]
      intro _ h
      rw [hps] at h
      exact hne (Option.some.inj h).symm
    simp [ind, this]
  · intro h; exact absurd hs h

theorem Nst_re (D : Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E))
    (κ : Pt E → Pt E → ℂ) (t t' : E) :
    (D.Nst ε i s w Y κ t t').re =
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * D.gram ε i w (join h s t) (join h' s t')).re / D.wt w := by
  simp only [Data.Nst, Complex.div_ofReal_re]

theorem Nst_nonneg (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ : Pt E → Pt E → ℂ} (hκ : PSDOn Y κ) (t : E) :
    0 ≤ (D.Nst ε i s w Y κ t t).re := by
  rw [Nst_re]
  refine div_nonneg ?_ (hW w).le
  exact psd_sum_nonneg (psd_mul hκ (psd_pull (fun h => join h s t) (hG ε hε i w _)))

theorem Nst_mono (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ₁ κ₂ : Pt E → Pt E → ℂ}
    (hκ : PSDOn Y (fun h h' => κ₂ h h' - κ₁ h h')) (t : E) :
    (D.Nst ε i s w Y κ₁ t t).re ≤ (D.Nst ε i s w Y κ₂ t t).re := by
  have h := Nst_nonneg D hG hW hε i s w Y hκ t
  have e : D.Nst ε i s w Y (fun h h' => κ₂ h h' - κ₁ h h') t t =
      D.Nst ε i s w Y κ₂ t t - D.Nst ε i s w Y κ₁ t t := by
    simp only [Data.Nst, sub_mul, Finset.sum_sub_distrib, sub_div]
  rw [e, Complex.sub_re] at h
  linarith

end

end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

namespace Formalism.FourierDecayAlt.P

open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

open Classical in
theorem splitByLastSize : Formalism.FourierDecayAlt.TB.SplitBySize := by
  intro E W _ D hG hK T ε hε i hi w
  have hM : PSDOn (T.X i) (fun p q => D.Kr i p q * D.gram ε i w p q) :=
    psd_mul (hK.1 i _) (hG ε hε i w _)
  have h := sqrt_form_sum_le _ hM (Icc 1 i) (fun s => ind (T.X i) (Xs T i s))
  have h2 : ∀ s, Xs T i s ⊆ T.X i := fun s => Finset.filter_subset _ _
  rw [sum_ind_Xs T hi, form_ind (T.X i) (T.X i) (Finset.Subset.refl _)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  simp only [fun s => form_ind (T.X i) (Xs T i s) (h2 s)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  exact h

open Classical in
theorem diagStep : Formalism.FourierDecayAlt.TB.DiagStep := by
  intro E W _ D hG hK hW hA T ε hε i s hs hsi hir w R hR
  obtain ⟨_, hdom, hper, _⟩ := hA i s hs hsi hir
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ h).1 hh).1
  have hnn : ∀ t₀ t : E, 0 ≤ (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re :=
    fun t₀ t => Nst_nonneg D hG hW hε i s w _ (hK.2 i s t₀ _) t
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold Data.Dg
  refine Finset.sum_le_sum fun t ht => ?_
  have ht0 : t ≠ 0 := fun h => T.zero_not_mem _ _ (h ▸ ht)
  obtain ⟨t₀, ht₀, hmem⟩ := hR t ht
  have h1 := Nst_mono D hG hW hε i s w (T.X (i - s)) (hdom t ht0 _ hY) t
  rw [hper t t₀ hmem] at h1
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun t₀ => if t - t₀ ∈ D.La (i - s + 1) s then
      (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re else 0)
    (fun x _ => by
      split_ifs
      · exact hnn x t
      · exact le_refl 0) ht₀
  simpa only [if_pos hmem] using h2

end Formalism.FourierDecayAlt.P
