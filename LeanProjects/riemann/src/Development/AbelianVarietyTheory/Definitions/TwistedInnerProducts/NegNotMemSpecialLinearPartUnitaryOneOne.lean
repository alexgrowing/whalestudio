import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.RealInd GlobalTheory.FlagMeas.Model

namespace GlobalTheory.LeviFactor.Model

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}

theorem uPart_fix_J {L : Submodule ℂ (Fin n → ℂ)} {g : UJ ε} (hg : g ∈ uPart ε L) {y : Fin n → ℂ} (hy : y ∈ L) :
    uMat g *ᵥ (Jm ε *ᵥ y) = Jm ε *ᵥ y := by
  have h := inv_mul_Jm (ε := ε) g⁻¹
  rw [inv_inv] at h
  rw [mulVec_mulVec, h, ← mulVec_mulVec, (((uPart ε L).inv_mem hg) y hy).2]

theorem uPart_le (hW : IsIsoFlag ε j W) : uPart ε (W (Fin.last a)) ≤ leviOne ε W := fun g hg => by
  have k : ∀ i, ∀ y ∈ W i, uMat g *ᵥ y = y ∧ (uMat g)ᴴ *ᵥ y = y := fun i y hy => hg y (hW.2.1 (Fin.le_last i) hy)
  refine ⟨fun i y hy => by rw [(k i y hy).1, (k i y hy).2]; exact ⟨hy, hy⟩, fun i => ?_⟩
  have := detOn_step (g := uMat g) (U := ⊥) (U' := W i) (c := 1) bot_le (d := Module.finrank ℂ (W i)) (by simp)
    (by simp) fun y hy => by simp [(k i y hy).1]
  simpa [detOn_bot] using this

theorem glPart_inf_uPart (hW : IsIsoFlag ε j W) : glPart ε W ⊓ uPart ε (W (Fin.last a)) = ⊥ := by
  refine eq_bot_iff.2 fun g ⟨h1, h2⟩ => ?_
  exact GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW g
    ⟨fun i y hy => by rw [(h2 y (hW.2.1 (Fin.le_last _) hy)).1, sub_self]; exact zero_mem _, h1.2⟩ _
    ((leviSub ε W).inv_mem h1.1.1) (by rw [mul_inv_cancel]; exact (compactSub ε).one_mem)

theorem glPart_zero {j : Fin 0 → ℕ} {W : Flag n 0} (hW : IsIsoFlag ε j W) : glPart ε W = ⊥ := by
  have h := glPart_inf_uPart hW
  rwa [show W (Fin.last 0) = ⊥ from hW.1, uPart_bot, inf_top_eq] at h

variable (ε) in

def neg : UJ ε := ⟨-1, by
  change inUJ ε (-1)
  simp [inUJ]⟩

theorem uMat_neg : uMat (neg ε) = -1 := rfl

theorem neg_mem_leviOne : neg ε ∈ leviOne ε W := by
  refine ⟨fun i y hy => by simpa [uMat_neg, neg_mulVec] using hy, fun i => ?_⟩
  have := detOn_step (g := uMat (neg ε)) (U := ⊥) (U' := W i) (c := -1) bot_le (d := Module.finrank ℂ (W i)) (by simp)
    (by simp) fun y hy => by simp [uMat_neg, neg_mulVec]
  simpa [detOn_bot] using this

theorem neg_mem_glPart_iff : neg ε ∈ glPart ε W ↔
    ∀ y : Fin n → ℂ, (∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) → y ∈ W (Fin.last a) := by
  have e : ∀ y : Fin n → ℂ, uMat (neg ε) *ᵥ y - y = (-2 : ℂ) • y := fun y => by
    rw [uMat_neg, neg_mulVec, one_mulVec]; module
  refine ⟨fun h y hy => ?_, fun h => ⟨neg_mem_leviOne, fun y hy => e y ▸ (W _).smul_mem _ (h y hy)⟩⟩
  have := h.2 y hy
  rwa [e, Submodule.smul_mem_iff _ (by norm_num)] at this

theorem neg_mem_slPart_iff : neg ε ∈ slPart ε W ↔ neg ε ∈ glPart ε W ∧ ∀ i, Even (Module.finrank ℂ (W i)) := by
  refine and_congr_right fun hg => forall_congr' fun i => ?_
  have e : ∀ h : ∀ y ∈ W i, Matrix.toLin' (uMat (neg ε)) y ∈ W i,
      LinearMap.det ((Matrix.toLin' (uMat (neg ε))).restrict h) = (-1) ^ Module.finrank ℂ (W i) := fun h => by
    rw [show (Matrix.toLin' (uMat (neg ε))).restrict h = (-1 : ℂ) • LinearMap.id by
      ext y : 2; simp [uMat_neg], LinearMap.det_smul]
    simp
  refine ⟨fun h => ?_, fun h k => by rw [e, h.neg_one_pow]⟩
  have := (e _).symm.trans (h fun y hy => (hg.1.1 i y hy).1)
  rwa [neg_one_pow_eq_one_iff_even (by norm_num)] at this

theorem neg_mem_generalLinearPart_unitary_one_one : neg e2 ∈ glPart e2 W2 := neg_mem_glPart_iff.2 fun y hy => by
  have h := hy ![1, 1] (Submodule.subset_span rfl)
  simp [Jm, e2, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.diagonal] at h
  refine Submodule.mem_span_singleton.2 ⟨y 0, ?_⟩
  ext i
  fin_cases i
  · simp
  · simp; linear_combination h

theorem neg_notMem_specialLinearPart_unitary_one_one : neg e2 ∉ slPart e2 W2 := fun h => by
  have h1 := (neg_mem_slPart_iff.1 h).2 1
  have h2 := isIsotropicFlag_unitary_one_one.2.2.1 0
  have h3 : Module.finrank ℂ (W2 1) = 1 := by
    refine h2.trans ?_
    change Module.finrank ℂ (⊥ : Submodule ℂ (Fin 2 → ℂ)) + 1 = 1
    simp
  rw [h3] at h1
  exact Nat.not_even_one h1

theorem mU_notMem_glPart : mU ∉ glPart e2 W2 := fun h => by
  have := locSize_mU
  have h0 := h.1.2 0
  have h1 := h.1.2 1
  change (detOn (uMat mU) (W2 1) / detOn (uMat mU) (W2 0)) ^ (-(1 : ℝ) / ((1 : ℕ) : ℝ)) = 1 / 2 at this
  rw [h0, h1] at this
  norm_num at this

def e4 : Fin 4 → Bool := ![true, true, false, false]

def emb : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![v 0, v 1, v 0, v 1]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

def W4 : Flag 4 1 := ![⊥, LinearMap.range emb]

theorem finrank_siegel_flag : Module.finrank ℂ (LinearMap.range emb) = 2 := by
  rw [LinearMap.finrank_range_of_inj]
  · simp
  · intro u v h
    ext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1

theorem isIsotropicFlag_siegel : IsIsoFlag e4 ![2] W4 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [W4]
  · intro i
    fin_cases i
    change Module.finrank ℂ (LinearMap.range emb) = Module.finrank ℂ (⊥ : Submodule ℂ (Fin 4 → ℂ)) + 2
    rw [finrank_siegel_flag, finrank_bot]
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    simp [Jm, e4, emb, dotProduct, Matrix.mulVec, Fin.sum_univ_four, Matrix.diagonal]

theorem neg_mem_specialLinearPart_siegel : neg e4 ∈ slPart e4 W4 ∧ neg e4 ≠ 1 := by
  refine ⟨neg_mem_slPart_iff.2 ⟨neg_mem_glPart_iff.2 fun y hy => ?_, fun i => ?_⟩, fun h => ?_⟩
  · have h0 := hy _ ⟨![1, 0], rfl⟩
    have h1 := hy _ ⟨![0, 1], rfl⟩
    simp [Jm, e4, emb, dotProduct, Matrix.mulVec, Fin.sum_univ_four, Matrix.diagonal] at h0 h1
    refine ⟨![y 0, y 1], ?_⟩
    ext i
    fin_cases i <;> simp [emb]
    · linear_combination h0
    · linear_combination h1
  · fin_cases i
    · change Even (Module.finrank ℂ (⊥ : Submodule ℂ (Fin 4 → ℂ)))
      simp
    · change Even (Module.finrank ℂ (LinearMap.range emb))
      rw [finrank_siegel_flag]; decide
  · have := congrArg (fun g => uMat g 0 0) h
    simp [uMat_neg, uMat_one] at this
    norm_num at this

def e3 : Fin 3 → Bool := ![true, false, true]

def refl3 : UJ e3 := ⟨⟨diagonal ![1, 1, -1], diagonal ![1, 1, -1],
    by ext i k; fin_cases i <;> fin_cases k <;> simp, by ext i k; fin_cases i <;> fin_cases k <;> simp⟩, by
    change inUJ e3 (diagonal ![1, 1, -1])
    unfold inUJ
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Jm, e3, Matrix.mul_apply, Matrix.diagonal]⟩

theorem reflection_mem_unitaryPart : refl3 ∈ uPart e3 (Submodule.span ℂ {![1, 1, 0]}) ∧ refl3 ≠ 1 ∧
    neg e3 ∉ uPart e3 (Submodule.span ℂ {![1, 1, 0]}) := by
  have e : uMat refl3 = diagonal ![1, 1, -1] := rfl
  refine ⟨fun y hy => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [e]
    constructor <;> ext i <;> fin_cases i <;> simp [mulVec_diagonal]
  · have := congrArg (fun g => uMat g 2 2) h
    simp [e, uMat_one] at this
    norm_num at this
  · have := congrFun (h _ (Submodule.subset_span rfl)).1 0
    simp [uMat_neg, neg_mulVec] at this
    norm_num at this

end GlobalTheory.LeviFactor.Model

end
