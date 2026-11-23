import Mathlib
import Formalism.HermitianCurvature.StatementTB

namespace Formalism.FourierDecayAlt.P.FormDomination

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data

open scoped ComplexOrder

theorem form_nonneg {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := (Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  have e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ
      ((Matrix.hadamard (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)).mulVec
        (fun _ => (1 : ℂ))) = ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b := by
    simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
      star_one, one_mul, mul_one]
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort Y]
  rw [e] at H
  exact (Complex.le_def.1 H).1

theorem form_dom {α ι : Type} (Y : Finset α) (R : Finset ι) (c : ℝ) (k g : α → α → ℂ)
    (Th : ι → α → α → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * k a b - ∑ t ∈ R, Th t a b)) (hg : PSDOn Y g) :
    ∑ t ∈ R, (∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b).re ≤
      c * (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := form_nonneg Y _ g h hg
  have e : ∑ a ∈ Y, ∑ b ∈ Y, ((c : ℂ) * k a b - ∑ t ∈ R, Th t a b) * g a b =
      (c : ℂ) * ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b -
        ∑ t ∈ R, ∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [e, Complex.sub_re, Complex.re_ofReal_mul] at H
  rw [← Complex.re_sum]
  linarith

theorem prob_le {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ) (M : ℝ)
    (hg : ∀ a ∈ S, g a ≤ M) : ∑ a ∈ S, θ a * g a ≤ M := by
  calc ∑ a ∈ S, θ a * g a ≤ ∑ a ∈ S, θ a * M :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hg a ha) (hθ.1 a)
    _ = M := by rw [← Finset.sum_mul, hθ.2.2, one_mul]

theorem prob_nonneg {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ)
    (hg : ∀ a ∈ S, 0 ≤ g a) : 0 ≤ ∑ a ∈ S, θ a * g a :=
  Finset.sum_nonneg fun a ha => mul_nonneg (hθ.1 a) (hg a ha)

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (form_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem sum_baseGram_le (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) :
    ∑ t ∈ R, D.N0 ε k w Y (Th t) ≤ c * D.N0 ε k w Y κ := by
  unfold Data.N0
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (form_dom Y R c κ _ Th h (hG ε hε k w Y)) (hW w).le

theorem mean_dom (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (S : Finset W) (θ : W → ℝ) (hθ : IsProb S θ)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (hc : 0 ≤ c) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) (M : ℝ)
    (hM : ∀ w' ∈ S, D.N0 ε k w' Y κ ≤ M) :
    ∑ t ∈ R, ∑ w' ∈ S, θ w' * D.N0 ε k w' Y (Th t) ≤ c * M := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  refine prob_le S θ _ hθ _ fun w' hw' => ?_
  exact (sum_baseGram_le D hG hW hε k w' Y R c κ Th h).trans (mul_le_mul_of_nonneg_left (hM w' hw') hc)

end Formalism.FourierDecayAlt.P.FormDomination

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.FormDomination

open Classical

theorem longBlockStep : Formalism.FourierDecayAlt.TB.MultiStep := by
  intro E W _ D C₄ hG hK hW hA hB hC hv T ε hε i s hs hsi hi w hw hcnt hvol R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hB ε hε i s hs hsi hi w hw hcnt hvol
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i s (by omega) hsi hi
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ _).1 hh).1
  have hc : 0 ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') :=
    mul_nonneg (pow_nonneg (by linarith) _) (Finset.prod_nonneg fun s' _ => hv _ _)
  have hd := hdom R hR (T.X (i - s)) hY
  have hd' : PSDOn (T.X (i - s)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - s) a b -
      ∑ t ∈ R, D.Th i s t a b) := by
    push_cast; exact hd
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg (i - s + 1) s).filter (fun t => t - t₀ ∈ D.La (i - s + 1) s),
            (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re
      ≤ ∑ t₀ ∈ R, C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        refine Finset.sum_le_sum fun t₀ _ => ?_
        refine hest (T.X (i - s)) hY _ (hK.2 i s t₀ _) t₀ _ fun t ht => ?_
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩
    _ = C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ t₀ ∈ R, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        rw [Finset.mul_sum]
    _ ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * ((1 + D.e i) * M) :=
        mul_le_mul_of_nonneg_left
          (mean_dom D hG hW hε (i - s) _ θ hθ _ R (1 + D.e i) (by linarith) _ _ hd' M hM) hc

theorem singleBlockStep : Formalism.FourierDecayAlt.TB.OneStep := by
  intro E W _ D ep hG hK hW hA hWv hP hL T ε hε i hi1 hi w hw hcnt R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hWv ε hε i hi1 hi w hw hcnt
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i 1 le_rfl hi1 hi
  have hii : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  rw [hii] at hdom
  have hY : ∀ h ∈ T.X (i - 1), level h = i - 1 := fun h hh => ((T.isTower _ _).1 hh).1
  have hep : 0 ≤ ep := by simpa using hL.1 i hi1 hi ∅ (by simp)
  have hd := hdom R hR (T.X (i - 1)) hY
  have hd' : PSDOn (T.X (i - 1)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - 1) a b -
      ∑ t ∈ R, D.Th i 1 t a b) := by
    push_cast; exact hd
  have h1e : 0 ≤ 1 + D.e i := by linarith

  set g : Finset (Fin D.f) → E → ℝ := fun A t₀ => ∑ w' ∈ D.Wb (D.cnt w + D.K),
    θ A w' * D.N0 ε (i - 1) w' (T.X (i - 1)) (D.Th i 1 t₀) with hg
  have hg0 : ∀ A t₀, 0 ≤ g A t₀ := fun A t₀ =>
    prob_nonneg _ _ _ (hθ A) fun w' _ => baseGram_nonneg D hG hW hε _ _ _ _ (hK.2 i 1 t₀ _)
  have hstep : ∀ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
      (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re ≤
        D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀ := by
    intro t₀ _
    have hpsd := hK.2 i 1 t₀ (T.X (i - 1))
    obtain ⟨h0, hl⟩ := hest (T.X (i - 1)) hY _ hpsd
    have hbound : ∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lad i ∧ l ≠ 0) →
        ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ ep * ∑ A, g A t₀ := by
      intro L hLm
      have hG0 : 0 ≤ ∑ A, g A t₀ := Finset.sum_nonneg fun A _ => hg0 A t₀
      have h1 : ∀ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤
          max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := by
        intro l hl'
        obtain ⟨A, hA'⟩ := hl l (hLm l hl').1 (hLm l hl').2
        calc ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ D.maj (D.szD i) l * g A t₀ := hA'
          _ ≤ max (D.maj (D.szD i) l) 0 * g A t₀ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (hg0 A t₀)
          _ ≤ max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ :=
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (f := fun A => g A t₀) (fun A _ => hg0 A t₀)
                  (Finset.mem_univ A)) (le_max_right _ _)
      have h2 : ∑ l ∈ L, max (D.maj (D.szD i) l) 0 ≤ ep := by
        have h3 := hL.1 i hi1 hi (L.filter fun l => 0 ≤ D.maj (D.szD i) l)
          (fun l hl' => hLm l (Finset.mem_filter.1 hl').1)
        rw [Finset.sum_filter] at h3
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) h3
        split_ifs with hh
        · exact max_eq_left hh
        · exact max_eq_right (not_le.1 hh).le
      calc ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖
          ≤ ∑ l ∈ L, max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := Finset.sum_le_sum h1
        _ = (∑ l ∈ L, max (D.maj (D.szD i) l) 0) * ∑ A, g A t₀ := by rw [Finset.sum_mul]
        _ ≤ ep * ∑ A, g A t₀ := mul_le_mul_of_nonneg_right h2 hG0
    have hp := hP ε hε i hi1 hi w (T.X (i - 1)) hY _ hpsd t₀ _ hbound
      ((T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1)) (fun t ht => by
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩)
    rw [h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (baseGram_nonneg D hG hW hε _ _ _ _ hpsd)] at hp
    exact hp
  have hsumG : ∑ t₀ ∈ R, ∑ A, g A t₀ ≤ 2 ^ D.f * ((1 + D.e i) * M) := by
    rw [Finset.sum_comm]
    calc ∑ A : Finset (Fin D.f), ∑ t₀ ∈ R, g A t₀
        ≤ ∑ _A : Finset (Fin D.f), (1 + D.e i) * M :=
          Finset.sum_le_sum fun A _ =>
            mean_dom D hG hW hε (i - 1) _ (θ A) (hθ A) _ R (1 + D.e i) h1e _ _ hd' M hM
      _ = 2 ^ D.f * ((1 + D.e i) * M) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
            (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re
      ≤ ∑ t₀ ∈ R, (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀) :=
        Finset.sum_le_sum hstep
    _ = ∑ t₀ ∈ R, D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) +
          ep * ∑ t₀ ∈ R, ∑ A, g A t₀ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 + D.e i) * D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) +
          ep * (2 ^ D.f * ((1 + D.e i) * M)) :=
        add_le_add (sum_baseGram_le D hG hW hε (i - 1) w _ R (1 + D.e i) _ _ hd')
          (mul_le_mul_of_nonneg_left hsumG hep)
    _ = (1 + D.e i) * (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) + 2 ^ D.f * ep * M) := by
        ring

end Formalism.FourierDecayAlt.P
