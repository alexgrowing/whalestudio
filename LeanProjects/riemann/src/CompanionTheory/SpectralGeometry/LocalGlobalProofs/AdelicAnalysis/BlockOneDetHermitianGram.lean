import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BlockAlg

section Entries

variable {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)

theorem blockOne_zero_zero : blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

end Entries

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : (blockOne t A).submatrix Fin.succ (Fin.succAbove (0 : Fin (M + 1))) = A := by
    ext i j
    simp [blockOne_succ_succ]
  rw [h0, Finset.sum_eq_zero]
  · simp [blockOne_zero_zero]
  · intro j _
    simp [blockOne_zero_succ]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_blockOne_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t a b : E)
    (x y : Fin M → E) :
    hE σ (blockOne t J) (Fin.cons a x : Fin (M + 1) → E) (Fin.cons b y : Fin (M + 1) → E) =
      σ a * t * b + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, blockOne_zero_zero,
    blockOne_zero_succ, blockOne_succ_zero, blockOne_succ_succ]
  simp

theorem hE_zero_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y : Fin M → E) :
    hE σ J 0 y = 0 := by
  simp [hE, hform]

theorem hE_zero_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    hE σ J x 0 = 0 := by
  simp [hE, hform]

theorem gramE_consTup (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : E) {n : ℕ}
    (X : Fin n → Fin M → E) :
    gramE σ (blockOne t J) (consTup X) = blockOne t (gramE σ J X) := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 1 (fun _ => 0)) = t
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 0 (X b)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 1 (fun _ => 0)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_right]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 0 (X b)) = hE σ J (X a) (X b)
    rw [hE_blockOne_cons]
    simp

theorem exists_consTup_of_gramE (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E}
    (ht : t ≠ 0) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E)
    (h0 : Y 0 = Fin.cons 1 (fun _ => 0)) (hY : gramE σ (blockOne t J) Y = blockOne t T) :
    ∃ X, gramE σ J X = T ∧ Y = consTup X := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hsplit : ∀ a : Fin n, Y a.succ = Fin.cons (Y a.succ 0) (Fin.tail (Y a.succ)) := fun a =>
    (Fin.cons_self_tail _).symm
  have hfirst : ∀ a : Fin n, Y a.succ 0 = 0 := by
    intro a
    have h := congrFun (congrFun hY 0) a.succ
    change hE σ (blockOne t J) (Y 0) (Y a.succ) = blockOne t T 0 a.succ at h
    rw [h0, hsplit a, hE_blockOne_cons, hz, hE_zero_left, blockOne_zero_succ] at h
    simpa [ht] using h
  have hY' : ∀ a : Fin n, Y a.succ = Fin.cons 0 (Fin.tail (Y a.succ)) := by
    intro a
    conv_lhs => rw [hsplit a, hfirst a]
  refine ⟨fun a => Fin.tail (Y a.succ), ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun hY a.succ) b.succ
    change hE σ (blockOne t J) (Y a.succ) (Y b.succ) = blockOne t T a.succ b.succ at h
    rw [hY' a, hY' b, hE_blockOne_cons, blockOne_succ_succ] at h
    change hE σ J (Fin.tail (Y a.succ)) (Fin.tail (Y b.succ)) = T a b
    simpa using h
  · funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · exact h0
    · exact hY' a

theorem block_alg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  intro F E _ _ _ _ _ σ _ M J t
  refine ⟨det_blockOne _ _, ?_, fun n X => gramE_consTup σ J _ X, ?_⟩
  · intro hJ a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simpa [blockOne_succ_succ] using hJ a b
  · intro ht n T Y h0 hY
    have ht' : algebraMap F E t ≠ 0 := by
      simpa using ht
    exact exists_consTup_of_gramE σ J ht' T Y h0 hY

end GlobalTheory.CompanionTheory.SW.BlockAlg
