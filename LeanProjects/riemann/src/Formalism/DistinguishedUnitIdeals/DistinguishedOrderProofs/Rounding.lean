import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

namespace Formalism.ExponentWindows

section Rounding

variable {K D : Type} [Field K] [AddCommGroup D] [Module K D]

lemma filt_eq_of_no_jump (Fil : ℤ → Submodule K D) (a c : ℤ) (hac : a ≤ c)
    (h : ∀ u, a ≤ u → u < c → Fil u = Fil (u+1)) : Fil a = Fil c := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = a + k := ⟨(c - a).toNat, by omega⟩
  clear hac
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 := ih (fun u h1 h2 => h u h1 (by omega))
    have e2 := h (a + k) (by omega) (by omega)
    rw [e1, e2]
    congr 1
    push_cast
    ring

lemma filt_eq_top_of_no_jump_below (Fil : ℤ → Submodule K D) (hA : Antitone Fil) (lo : ℤ) (hlo : Fil lo = ⊤) (a : ℤ)
    (h : ∀ u, u < a → Fil u = Fil (u+1)) : ∀ u, u ≤ a → Fil u = ⊤ := by
  intro u hu
  rcases le_or_gt u lo with hul | hul
  · exact top_unique (by rw [← hlo]; exact hA hul)
  · rw [← filt_eq_of_no_jump Fil lo u hul.le (fun v _ h2 => h v (by omega)), hlo]

lemma filt_eq_bot_of_no_jump_above (Fil : ℤ → Submodule K D) (hA : Antitone Fil) (hi : ℤ) (hhi : Fil hi = ⊥) (a : ℤ)
    (h : ∀ u, a ≤ u → Fil u = Fil (u+1)) : ∀ u, a ≤ u → Fil u = ⊥ := by
  intro u hu
  rcases le_or_gt hi u with hul | hul
  · exact le_bot_iff.mp (by rw [← hhi]; exact hA hul)
  · rw [filt_eq_of_no_jump Fil u hi hul.le (fun v h1 _ => h v (by omega)), hhi]

lemma filt_eq_of_no_jump_between (Fil : ℤ → Submodule K D) (a c : ℤ)
    (h : ∀ u, a ≤ u → u < c → Fil u = Fil (u+1)) : ∀ u, a ≤ u → u ≤ c → Fil u = Fil c := by
  intro u hu huc
  exact filt_eq_of_no_jump Fil u c huc (fun v h1 h2 => h v (by omega) h2)

theorem filtration_rounding : Rounding := by
  unfold Rounding
  intro K D _ _ _ Fil G S η g b hF hG hS hη hGg hSg hηg hgb
  simp only [IsFilt, NbThin, NbUp, NbDown] at hF ⊢
  obtain ⟨hA, ⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hF
  refine ⟨fun hj i => ?_, fun hj i => ?_, fun hj i => ?_⟩
  · have top : ∀ u, u ≤ -G → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-G)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, G + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (G + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1
      · exact bot_le
      · rw [top (-i) (by omega)]
    · split_ifs with h1
      · rw [bot (-i) (by omega)]
      · exact le_top
  · have top : ∀ u, u ≤ -η → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-η)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, b + S + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (b + S + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have mid : ∀ u, η + 1 ≤ u → u ≤ b → Fil u = Fil b :=
      filt_eq_of_no_jump_between Fil (η + 1) b
        (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1 h2
      · exact bot_le
      · exact hA (show -i ≤ b by omega)
      · rw [top (-i) (by omega)]
    · split_ifs with h1 h2
      · rw [bot (-i) (by omega)]
      · rcases le_or_gt b (-i) with h3 | h3
        · exact hA h3
        · rw [mid (-i) (by omega) (by omega)]
      · exact le_top
  · have top : ∀ u, u ≤ -b - S → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-b - S)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, η + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (η + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have mid : ∀ u, -b + 1 ≤ u → u ≤ -η → Fil u = Fil (-η) :=
      filt_eq_of_no_jump_between Fil (-b + 1) (-η)
        (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1 h2
      · exact bot_le
      · exact hA (show -i ≤ -η by omega)
      · rw [top (-i) (by omega)]
    · split_ifs with h1 h2
      · rw [bot (-i) (by omega)]
      · rcases le_or_gt (-η) (-i) with h3 | h3
        · exact hA h3
        · rw [mid (-i) (by omega) (by omega)]
      · exact le_top

end Rounding

end Formalism.ExponentWindows
