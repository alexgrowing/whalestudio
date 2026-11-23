import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.CapelliFoldBound

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def UnifOp (o : ℕ) (Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ F, CkOn (⊤ : ℕ∞) (GV k r) F → CkOn (⊤ : ℕ∞) (GV k r) (Θ F)) ∧
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), CkOn (⊤ : ℕ∞) (GV k r) F →
    CCle A (m + o) F b → CCle A m (Θ F) (K * b)

variable {Wp Wq}

theorem UnifOp.congr {o : ℕ} {Θ Θ' : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h : UnifOp Wp Wq o Θ) (e : ∀ F, Θ' F = Θ F) : UnifOp Wp Wq o Θ' := by
  have : Θ' = Θ := funext e
  rw [this]; exact h

theorem UnifOp.mono {o o' : ℕ} (ho : o ≤ o')
    {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)} (h : UnifOp Wp Wq o Θ) : UnifOp Wp Wq o' Θ := by
  obtain ⟨h1, K, hK, h2⟩ := h
  exact ⟨h1, K, hK, fun A m F b hF hF' => h2 A m F b hF (pd_ccle_mono le_rfl (by omega) hF')⟩

theorem UnifOp.comp {o₁ o₂ o : ℕ} (ho : o₁ + o₂ ≤ o)
    {Θ₁ Θ₂ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)} (h₁ : UnifOp Wp Wq o₁ Θ₁)
    (h₂ : UnifOp Wp Wq o₂ Θ₂) : UnifOp Wp Wq o (fun F => Θ₁ (Θ₂ F)) := by
  obtain ⟨s1, K₁, hK₁, h1⟩ := h₁
  obtain ⟨s2, K₂, hK₂, h2⟩ := h₂
  refine ⟨fun F hF => s1 _ (s2 F hF), K₁ * K₂, mul_nonneg hK₁ hK₂, fun A m F b hF hF' => ?_⟩
  rw [mul_assoc]
  exact h1 A m _ _ (s2 F hF) (h2 A (m + o₁) F b hF (pd_ccle_mono le_rfl (by omega) hF'))

theorem UnifOp.add {o : ℕ} {Θ₁ Θ₂ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : UnifOp Wp Wq o Θ₁) (h₂ : UnifOp Wp Wq o Θ₂) : UnifOp Wp Wq o (fun F g => Θ₁ F g + Θ₂ F g) := by
  obtain ⟨s1, K₁, hK₁, h1⟩ := h₁
  obtain ⟨s2, K₂, hK₂, h2⟩ := h₂
  refine ⟨fun F hF => Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (s1 F hF) (s2 F hF), K₁ + K₂, add_nonneg hK₁ hK₂,
    fun A m F b hF hF' => ?_⟩
  rw [add_mul]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (h1 A m F b hF hF') (h2 A m F b hF hF')

end GlobalTheory.CapelliFoldBound

namespace GlobalTheory

open Filter Topology MeasureTheory in
private theorem ckOn_sum_smul_Rw {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (L : List (ℂ × List (_root_.Formalism.FourierDecayAlt.B.Mat k r))) (hL : ∀ cw ∈ L, ∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X)
    {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)} (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) :
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => (L.map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum) := by
  induction L with
  | nil => exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_zero'
  | cons cw L ih =>
    have hw : ∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.inLie k r X := by
      intro X hX
      have := hL cw (List.mem_cons_self ..) X hX
      unfold _root_.Formalism.FourierDecayAlt.B.unitLie at this
      unfold _root_.Formalism.FourierDecayAlt.B.inLie
      exact this.1
    exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_add' (_root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' cw.1 (_root_.Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF cw.2 hw)) (ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h))

open Filter Topology MeasureTheory in
private theorem capelli_eq_foldT_signed_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (y : ℂ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.Q.CV k r y F g = ∑ σ : Equiv.Perm (Fin (2 * (r - 0) + k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
        (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j)) F g := by
  unfold _root_.Formalism.FourierDecayAlt.Q.CV _root_.Formalism.FourierDecayAlt.Q.capL _root_.Formalism.QuantumDeterminants.qminorOp _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT
  simp only [Finset.sum_apply, List.map_ofFn, Pi.smul_apply, Function.comp_def]
  rfl

open Filter Topology MeasureTheory in
private theorem capelli_eq_wordSum_lemma_3 {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (y : ℂ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E) (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) :
    ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r y F g =
      ∑ σ : Equiv.Perm (Fin (2 * (r - 0) + k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
          (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j))).map
            fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum := by
  intro g hg
  rw [capelli_eq_foldT_signed_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hloc : _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (⊤ : ℕ∞) F g := by
    unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF
    exact hF g hg
  rw [_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq _ F g hg (_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top hloc)]

open Filter Topology MeasureTheory in
private theorem CCle_sum_smul_Rw {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N : ℕ) (L : List (ℂ × List (_root_.Formalism.FourierDecayAlt.B.Mat k r)))
    (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ N) {A : ℝ} {m : ℕ}
    {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} {c : ℝ} (hF : _root_.Formalism.FourierDecayAlt.B.CCle A (m + N) F c) :
    _root_.Formalism.FourierDecayAlt.B.CCle A m (fun g => (L.map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      ((L.map fun cw => ‖cw.1‖).sum * c) := by
  induction L with
  | nil => simpa using (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))
  | cons cw L ih =>
    have hcw := hL cw (List.mem_cons_self ..)
    have h1 : _root_.Formalism.FourierDecayAlt.B.CCle A m (_root_.Formalism.FourierDecayAlt.B.Rw cw.2 F) c :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hcw.1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by omega) hF)
    have h2 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 h1) (ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact h2

open Filter Topology MeasureTheory in
private theorem norm_sign_perm_complex_eq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

open Filter Topology MeasureTheory in
private theorem capelli_smooth_and_bound_lemma {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (y : ℂ) :
    (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (_root_.Formalism.FourierDecayAlt.Q.CV k r y F)) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (m : ℕ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ),
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → _root_.Formalism.FourierDecayAlt.B.CCle A (m + (2 * r + k + 1)) F c →
        _root_.Formalism.FourierDecayAlt.B.CCle A m (_root_.Formalism.FourierDecayAlt.Q.CV k r y F) (K * c) := by
  set ts : Equiv.Perm (Fin (2 * (r - 0) + k + 1)) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
      (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j) with hts
  have hwords : ∀ σ, ∀ cw ∈ _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ),
      (∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1 := by
    intro σ cw hcw
    obtain ⟨h1, h2⟩ := _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (ts σ) cw hcw
    refine ⟨h1, h2.trans ?_⟩
    simp [hts]
  refine ⟨fun F hF => ?_, ?_⟩
  · have hG := _root_.Formalism.FourierDecayAlt.P.JCx2.sq_ckOn_sum (Finset.univ : Finset (Equiv.Perm (Fin (2 * (r - 0) + k + 1))))
      (fun σ g => ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      (fun σ _ => _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (ckOn_sum_smul_Rw _ (fun cw h => (hwords σ cw h).1) hF))
    have heq := capelli_eq_wordSum_lemma_3 y F hF
    unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hG ⊢
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hG g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun x hx hxG => (heq x hxG).trans (hagree x hx hxG)⟩
  · refine ⟨∑ σ, ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => ‖cw.1‖).sum,
      Finset.sum_nonneg fun σ _ => List.sum_nonneg fun a ha => by
        obtain ⟨cw, -, rfl⟩ := List.mem_map.1 ha
        exact norm_nonneg _, ?_⟩
    intro A m F c hF hc
    have hc0 : 0 ≤ c := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
    have hsum := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_sum (Finset.univ : Finset (Equiv.Perm (Fin (2 * (r - 0) + k + 1))))
      (fun σ g => ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      (fun σ => ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ * (((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => ‖cw.1‖).sum * c))
      (fun σ _ => _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ (CCle_sum_smul_Rw _ _ (hwords σ) hc))
    simp only [norm_sign_perm_complex_eq_one, one_mul] at hsum
    rw [Finset.sum_mul]
    exact _root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => (capelli_eq_wordSum_lemma_3 y F hF g hg).symm) hsum

open Filter Topology MeasureTheory in

theorem _root_.GlobalTheory.capelli_fold_ccle : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ)) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (A c : ℝ) (X : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) X → _root_.Formalism.FourierDecayAlt.B.CCle A (m + w.length * (2 * r + k + 1)) X c → _root_.Formalism.FourierDecayAlt.B.CCle A m (List.foldr (fun (a : Bool × ℝ) G => s • _root_.Formalism.FourierDecayAlt.Q.CV k r (a.2 : ℂ) G) (X) w) (K * c) := by
  intro k r Wp Wq _ _ _ _ _ _ s w
  have hsmooth : ∀ (w : List (Bool × ℝ)) (X : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) X →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (List.foldr (fun (a : Bool × ℝ) G => s • _root_.Formalism.FourierDecayAlt.Q.CV k r (a.2 : ℂ) G) X w) := by
    intro w X hX
    induction w with
    | nil => exact hX
    | cons a w ih => exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' s ((capelli_smooth_and_bound_lemma (a.2 : ℂ)).1 _ ih)
  induction w with
  | nil => exact fun m => ⟨1, zero_le_one, fun A c X _ hX => by simpa using hX⟩
  | cons a w ih =>
    intro m
    obtain ⟨K, hK, hbound⟩ := ih (m + (2 * r + k + 1))
    obtain ⟨Ky, hKy, hy⟩ := (capelli_smooth_and_bound_lemma (Wp := Wp) (Wq := Wq) (a.2 : ℂ)).2
    refine ⟨‖s‖ * (Ky * K), by positivity, fun A c X hX hXc => ?_⟩
    have h1 := hbound A c X hX (by
      have : m + (2 * r + k + 1) + w.length * (2 * r + k + 1) = m + (a :: w).length * (2 * r + k + 1) := by
        simp only [List.length_cons]; ring
      rw [this]; exact hXc)
    have h2 := hy A m _ (K * c) (hsmooth w X hX) h1
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s h2
    simp only [List.foldr_cons]
    rw [show ‖s‖ * (Ky * K) * c = ‖s‖ * (Ky * (K * c)) by ring]
    exact h3

end GlobalTheory
