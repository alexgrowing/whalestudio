import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.UnipRead

variable {E : Type} [Field E] {M c : ℕ}

def lv (M u : ℕ) : ℕ := if u < M then 1 else u - M + 1

theorem one_le_lv (M u : ℕ) : 1 ≤ lv M u := by unfold lv; split_ifs <;> omega

def Unip (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) : Prop :=
  ∀ u v : Fin (M + c), lv M v.1 ≤ lv M u.1 → x (Pi.single v 1) u = if u = v then 1 else 0

theorem apply_eq_sum (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) (w : Fin (M + c) → E) (l : Fin (M + c)) :
    x w l = ∑ v, w v * x (Pi.single v 1) l := by
  have hw : w = ∑ v, Pi.single v (w v) := (Finset.univ_sum_single w).symm
  conv_lhs => rw [hw]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : (Pi.single v (w v) : Fin (M + c) → E) = w v • (Pi.single v (1 : E) : Fin (M + c) → E) := by
    ext j; simp [Pi.single_apply]
  rw [h, map_smul]
  simp

theorem eN_val (v : Fin (M + c)) : Loc.eN E (M + c) v.1 = Pi.single v 1 := by
  ext l; simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_out {j : ℕ} (h : ¬ j < M + c) : Loc.eN E (M + c) j = 0 := by
  ext l; simp only [Loc.eN, Pi.zero_apply]; rw [if_neg]; omega

theorem inX_apply (y : Fin M → E) (l : Fin (M + c)) :
    Loc.inX E M c y l = if h : l.1 < M then y ⟨l.1, h⟩ else 0 := by
  simp only [Loc.inX, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem col {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) (j : ℕ) (l : Fin (M + c))
    (hle : lv M j ≤ lv M l.1) : x (Loc.eN E (M + c) j) l = Loc.eN E (M + c) j l := by
  by_cases h : j < M + c
  · have := eN_val (E := E) (⟨j, h⟩ : Fin (M + c))
    simp only at this
    rw [this, hU l ⟨j, h⟩ hle]
    simp [Pi.single_apply]
  · rw [eN_out h, map_zero]

theorem r1cond_of_unip {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) : Loc.R1cond E M c x := by
  refine ⟨fun i w hw l hl => ?_, ?_, fun i l hl => ?_⟩
  · rw [apply_eq_sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v.1 < M + i
    · have hl' : ¬ l.1 < M + i := hl
      rw [hU l v (by unfold lv; split_ifs <;> omega), if_neg (by intro h; subst h; exact hl' hv), mul_zero]
    · rw [hw v hv, zero_mul]
  · ext l
    exact col hU M l (by have := one_le_lv M l.1; unfold lv at this ⊢; simp; omega)
  · have hl' : ¬ l.1 < M + i := hl
    show x _ l - _ = 0
    rw [col hU (M + i) l (by unfold lv; split_ifs <;> omega), sub_self]

theorem fixX_of_unip {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) : x ∈ Loc.fixX E M c := by
  intro y
  ext l
  rw [apply_eq_sum, Finset.sum_eq_single l]
  · by_cases hl : l.1 < M
    · rw [hU l l (le_refl _), if_pos rfl, mul_one]
    · simp [inX_apply, hl]
  · intro v _ hvl
    by_cases hv : v.1 < M
    · rw [hU l v (by have := one_le_lv M l.1; unfold lv; rw [if_pos hv]; exact this), if_neg (Ne.symm hvl), mul_zero]
    · rw [inX_apply, dif_neg hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem unip_of {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hR : Loc.R1cond E M c x)
    (hX : x ∈ Loc.fixX E M c) : Unip x := by
  intro u v hle
  by_cases hv : v.1 < M
  · have hs : (Pi.single v 1 : Fin (M + c) → E) = Loc.inX E M c (Pi.single ⟨v.1, hv⟩ 1) := by
      ext l; rw [inX_apply]; split_ifs with h
      · simp [Pi.single_apply, Fin.ext_iff]
      · simp [Pi.single_apply, Fin.ext_iff]; omega
    rw [hs, hX, ← hs]
    simp [Pi.single_apply]
  · have hj : M + (v.1 - M) = v.1 := by omega
    by_cases hu : u.1 < M + (v.1 - M)
    · have hvM : v.1 = M := by
        unfold lv at hle; split_ifs at hle <;> omega
      have h2 := congrFun hR.2.1 u
      have h4 := eN_val (E := E) v
      rw [hvM] at h4
      rw [h4] at h2
      rw [h2]; simp [Pi.single_apply]
    · have h3 := hR.2.2 (v.1 - M) u hu
      rw [hj, eN_val] at h3
      have h3' : x (Pi.single v 1) u - (Pi.single v 1 : Fin (M + c) → E) u = 0 := h3
      rw [sub_eq_zero] at h3'
      rw [h3']; simp [Pi.single_apply]

section Read
variable {k : Type} [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
  (e : A ⊕ Fin c ≃ Fin (M + c)) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem lev_eq (s : A ⊕ Fin c) : lev 1 s = lv M (e s).1 := by
  rcases s with a | i
  · have := eX_lt e rfl he a
    simp [lev, lv, this]
  · simp only [lev, Sum.elim_inr, lv, he i]
    split_ifs <;> omega

include he in

theorem inN_iff (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) : InN 1 (locHom ι e x) ↔ Unip x := by
  have hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r)) := fun r s => rfl
  have hent : ∀ (a : E) (r s : A ⊕ Fin c),
      ι a = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s ↔ a = if e r = e s then 1 else 0 := by
    intro a r s
    rw [Matrix.one_apply]
    by_cases h : r = s
    · simp [h, map_eq_one_iff ι ι.injective]
    · simp [h, e.injective.eq_iff]
  constructor
  · intro h u v hle
    have := h (e.symm u) (e.symm v) (by rw [lev_eq e he, lev_eq e he]; simpa using hle)
    rw [hval, hent] at this
    simpa using this
  · intro h r s hle
    rw [hval, hent]
    rw [lev_eq e he, lev_eq e he] at hle
    exact h (e r) (e s) hle

end Read

theorem mem_N1_iff_local_hom : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
    (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) →
    ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1 := by
  intro E k _ _ ι A _ _ M c c' e hcc he x
  subst hcc
  rw [Model.mem_N_iff, inN_iff ι e he]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact unip_of h1 h2
  · intro h
    have hN : locHom ι e x ∈ N k A c' 1 := Model.mem_N_iff.2 ((inN_iff ι e he x).2 h)
    have hinv : Unip x⁻¹ := by
      rw [← inN_iff ι e he, map_inv]
      exact Model.mem_N_iff.1 (inv_mem hN)
    exact ⟨⟨r1cond_of_unip h, r1cond_of_unip hinv⟩, fixX_of_unip h⟩

end GlobalTheory.UnipRead
