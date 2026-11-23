import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.StepOne

open Matrix MvPolynomial
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCompose

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DegDP : Prop := ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Vr N) ℂ),
  (dP X q).totalDegree ≤ q.totalDegree

def DegD : Prop := ∀ k j ρ : ℕ, (qD k j ρ).totalDegree ≤ j ∧ (qDb k j ρ).totalDegree ≤ j

def Expand : Prop := ∀ (k j ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ)
    (F : Mat k (j + ρ) → E), CkOn (m : ℕ∞) (GV k (j + ρ)) F →
    ∀ (w : List (Mat k (j + ρ))) (L : FS k (j + ρ)), (∀ X ∈ w, inLie k (j + ρ) X) →
    (∀ e ∈ L, ∀ X ∈ e.2, inLie k (j + ρ) X) → (∀ e ∈ L, e.2.length + w.length ≤ m) →
    ∀ g ∈ GV k (j + ρ), DjU k j ρ g ≠ 0 →
      Rw w (shape k j ρ F L) g = shape k j ρ F (steps k j ρ w L) g

def Bd (k j ρ κ ℓ : ℕ) (L : FS k (j + ρ)) : Prop :=
  ∀ e ∈ L, e.1.1.totalDegree ≤ κ ∧ e.2.length ≤ ℓ ∧ ∀ X ∈ e.2, inLie k (j + ρ) X

theorem Bd.mono {k j ρ κ ℓ κ' ℓ' : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) (hκ : κ ≤ κ')
    (hℓ : ℓ ≤ ℓ') : Bd k j ρ κ' ℓ' L :=
  fun e he => ⟨(h e he).1.trans hκ, (h e he).2.1.trans hℓ, (h e he).2.2⟩

theorem deg_cmul (c : ℂ) {N : ℕ} (q r : MvPolynomial (Vr N) ℂ) :
    (C c * q * r).totalDegree ≤ q.totalDegree + r.totalDegree := by
  refine (totalDegree_mul _ _).trans (Nat.add_le_add_right ?_ _)
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_C]

theorem bd_step (hP : DegDP) (hD : DegD) {k j ρ κ ℓ : ℕ} {X : Mat k (j + ρ)} (hX : inLie k (j + ρ) X)
    {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) : Bd k j ρ (κ + j) (ℓ + 1) (step k j ρ X L) := by
  intro e he
  rw [step, List.mem_flatMap] at he
  obtain ⟨e₀, he₀, hmem⟩ := he
  obtain ⟨hdeg, hlen, hlie⟩ := h e₀ he₀
  simp only [stepOne, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact ⟨(hP _ _ _).trans (hdeg.trans (Nat.le_add_right _ _)), hlen.trans (Nat.le_succ _), hlie⟩
  · exact ⟨(deg_cmul _ _ _).trans (Nat.add_le_add hdeg ((hP _ _ _).trans (hD k j ρ).1)),
      hlen.trans (Nat.le_succ _), hlie⟩
  · exact ⟨(deg_cmul _ _ _).trans (Nat.add_le_add hdeg ((hP _ _ _).trans (hD k j ρ).2)),
      hlen.trans (Nat.le_succ _), hlie⟩
  · refine ⟨hdeg.trans (Nat.le_add_right _ _), by simpa using hlen, ?_⟩
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact hX
    · exact hlie Y hY

theorem bd_steps (hP : DegDP) (hD : DegD) {k j ρ κ ℓ : ℕ} {w : List (Mat k (j + ρ))}
    (hw : ∀ X ∈ w, inLie k (j + ρ) X) {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (κ + j * w.length) (ℓ + w.length) (steps k j ρ w L) := by
  induction w with
  | nil => simpa [steps] using h
  | cons X w ih =>
    have h1 := bd_step hP hD (hw X (by simp)) (ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)))
    show Bd k j ρ _ _ (step k j ρ X (steps k j ρ w L))
    exact h1.mono (le_of_eq (by rw [List.length_cons]; ring)) (le_of_eq (by rw [List.length_cons]; ring))

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := by
  unfold hsVec
  ext i
  simp

open Classical in

def mkTerm (k j ρ : ℕ) (e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))) : DTerm k (j + ρ) Wp Wq where
  coef g := sv k j ρ e.1 g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := (starRingEnd ℂ) (sv k j ρ e.1 g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := if ∀ X ∈ e.2, inLie k (j + ρ) X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.conj_conj]

theorem mkTerm_word {k j ρ : ℕ} {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))}
    (h : ∀ X ∈ e.2, inLie k (j + ρ) X) : (mkTerm (Wp := Wp) (Wq := Wq) k j ρ e).word = e.2 := by
  first
  | exact if_pos h
  | (show (if ∀ X ∈ e.2, inLie k (j + ρ) X then e.2 else []) = e.2; exact if_pos h)
  | (simp only [mkTerm]; exact if_pos h)

theorem toFS {k j ρ o κ : ℕ} {Θ : DiffOp k (j + ρ) Wp Wq} (h : InDD k j ρ o κ Θ) :
    ∃ L : FS k (j + ρ), Bd k j ρ κ o L ∧ ∀ H g, opApply Θ H g = shape k j ρ H L g := by
  induction Θ with
  | nil => exact ⟨[], fun e he => by simp at he, fun H g => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨L, hL, hEq⟩ := ih (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨hlen, P, a, b, ⟨q, hq, hPq⟩, hc⟩ := h T (by simp)
    refine ⟨((q, a, b), T.word) :: L, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hq, hlen, T.word_lie⟩
      · exact hL e he
    · intro H g
      have e1 : opApply (T :: Θ) H g = T.coef g (Rw T.word H g) + opApply Θ H g := by
        simp [opApply]
      rw [e1, hEq H g, hc g]
      simp only [shape, List.map_cons, List.sum_cons, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply]
      congr 1
      rw [hPq g]
      rfl

theorem opApply_mk {k j ρ : ℕ} (L : FS k (j + ρ)) (hL : ∀ e ∈ L, ∀ X ∈ e.2, inLie k (j + ρ) X)
    (F : Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (g : Mat k (j + ρ)) :
    opApply (L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ)) F g = shape k j ρ F L g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  try simp only [Function.comp_apply]
  rw [mkTerm_word (hL e he)]
  first
  | rfl
  | simp [mkTerm]

theorem inDD_mk {k j ρ κ o : ℕ} (L : FS k (j + ρ)) (h : Bd k j ρ κ o L) :
    InDD k j ρ o κ (L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ)) := by
  intro T hT
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hT
  obtain ⟨hdeg, hlen, hlie⟩ := h e he
  refine ⟨by rw [mkTerm_word hlie]; exact hlen, fun g => eval (vars g) e.1.1, e.1.2.1, e.1.2.2,
    ⟨e.1.1, hdeg, fun g => rfl⟩, fun g => rfl⟩

end ops

theorem sv_mul {k j ρ : ℕ} (s t : SC (2 * (j + ρ) + k + 1)) (g : Mat k (j + ρ)) :
    sv k j ρ (mulSC s t) g = sv k j ρ s g * sv k j ρ t g := by
  simp only [sv, mulSC, map_mul, pow_add]
  ring

section sums

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem shape_mul {k j ρ : ℕ} (F : Mat k (j + ρ) → E) (s : SC (2 * (j + ρ) + k + 1)) (M : FS k (j + ρ))
    (g : Mat k (j + ρ)) :
    shape k j ρ F (M.map fun e => (mulSC s e.1, e.2)) g = sv k j ρ s g • shape k j ρ F M g := by
  induction M with
  | nil => simp [shape]
  | cons e M ih =>
    simp only [shape, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, sv_mul, mul_smul, smul_add]

theorem shape_flatMap {k j ρ : ℕ} (F : Mat k (j + ρ) → E) (L : FS k (j + ρ))
    (f : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ)) → FS k (j + ρ)) (g : Mat k (j + ρ)) :
    shape k j ρ F (L.flatMap f) g = (L.map fun e => shape k j ρ F (f e) g).sum := by
  induction L with
  | nil => simp [shape]
  | cons e L ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp only [shape, List.map_append, List.sum_append]

end sums

theorem composeDD_of (hP : DegDP) (hD : DegD) (hE : Expand) : ComposeDD := by
  intro k j ρ Wp Wq _ _ _ _ _ o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂
  obtain ⟨L₁, hB₁, hE₁⟩ := toFS h₁
  obtain ⟨L₂, hB₂, hE₂⟩ := toFS h₂
  set L : FS k (j + ρ) :=
    L₁.flatMap fun e₁ => (steps k j ρ e₁.2 L₂).map fun e => (mulSC e₁.1 e.1, e.2) with hLdef
  have hB : Bd k j ρ (κ₁ + κ₂ + j * o₁) (o₁ + o₂) L := by
    intro e he
    rw [hLdef, List.mem_flatMap] at he
    obtain ⟨e₁, he₁, he⟩ := he
    rw [List.mem_map] at he
    obtain ⟨e₂, he₂, rfl⟩ := he
    obtain ⟨d₁, l₁, lie₁⟩ := hB₁ e₁ he₁
    obtain ⟨d₂, l₂, lie₂⟩ := bd_steps hP hD lie₁ hB₂ e₂ he₂
    refine ⟨?_, ?_, lie₂⟩
    · calc (e₁.1.1 * e₂.1.1).totalDegree ≤ e₁.1.1.totalDegree + e₂.1.1.totalDegree :=
            totalDegree_mul _ _
        _ ≤ κ₁ + (κ₂ + j * o₁) :=
            Nat.add_le_add d₁ (d₂.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ l₁) _))
        _ = κ₁ + κ₂ + j * o₁ := by ring
    · show e₂.2.length ≤ o₁ + o₂
      omega
  refine ⟨L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ), inDD_mk L hB, ?_⟩
  intro F hF g hg hDg
  rw [opApply_mk L (fun e he => (hB e he).2.2) F g, hE₁]
  have hfun : opApply Θ₂ F = shape k j ρ F L₂ := funext (hE₂ F)
  rw [hfun, hLdef, shape_flatMap]
  show _ = (L₁.map fun e => sv k j ρ e.1 g • Rw e.2 (shape k j ρ F L₂) g).sum
  congr 1
  apply List.map_congr_left
  intro e₁ he₁
  rw [shape_mul, hE k j ρ _ (o₁ + o₂) F hF e₁.2 L₂ (hB₁ e₁ he₁).2.2 (fun e he => (hB₂ e he).2.2)
    (fun e he => by have := (hB₂ e he).2.1; have := (hB₁ e₁ he₁).2.1; omega) g hg hDg]

end PI.UnitaryGroupMassFormula.UsCompose
