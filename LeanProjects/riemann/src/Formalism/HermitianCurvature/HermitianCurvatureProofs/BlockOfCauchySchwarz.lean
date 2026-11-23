import Formalism.HermitianCurvature.StatementKB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound

open Finset
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

section block

variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)

noncomputable def qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) (c : γ → ℂ) : ℂ :=
  ∑ x ∈ Y, ∑ y ∈ Y, conj (c x) * k x y * c y

def blockK (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) : α ⊕ β → α ⊕ β → ℂ :=
  fun x y => match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) :
    KB.BlockPSD Y₁ Y₂ a w b ↔ TB.PSDOn (Y₁.disjSum Y₂) (blockK a w b) := by
  unfold KB.BlockPSD blockK
  exact Iff.rfl

theorem qf_block (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) (c : α ⊕ β → ℂ) :
    (qf (Y₁.disjSum Y₂) (blockK a w b) c).re =
      (qf Y₁ a (fun p => c (.inl p))).re + (qf Y₂ b (fun q => c (.inr q))).re +
        2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)).re := by
  have hconj : (∑ x ∈ Y₂, ∑ y ∈ Y₁, conj (c (.inr x)) * conj (w y x) * c (.inl y)) =
      conj (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)) := by
    rw [Finset.sum_comm]
    simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [qf, Finset.sum_disjSum, blockK, Finset.sum_add_distrib]
  rw [hconj]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem psd_iff_qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) :
    TB.PSDOn Y k ↔ (∀ x ∈ Y, ∀ y ∈ Y, k y x = conj (k x y)) ∧ ∀ c, 0 ≤ (qf Y k c).re := by
  classical
  have hqf : ∀ c : γ → ℂ, qf Y k c = ∑ i : Y, ∑ j : Y, conj (c i) * k i j * c j := by
    intro c
    unfold qf
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have hsum : ∀ x : Y →₀ ℂ,
      (x.sum fun i xi => x.sum fun j xj => star xi * Matrix.of (fun x y : Y => k x y) i j * xj) =
        ∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j := by
    intro x
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
    rfl
  unfold TB.PSDOn Matrix.PosSemidef
  constructor
  · rintro ⟨hH, hpos⟩
    refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
    · have h1 := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
      exact h1.symm
    · have h2 := hpos (Finsupp.equivFunOnFinite.symm fun i : Y => c i)
      rw [hsum] at h2
      rw [hqf]
      simpa using (Complex.le_def.mp h2).1
  · rintro ⟨hh, hq⟩
    refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
    · simp only [Matrix.of_apply]
      rw [hh j j.2 i i.2]
      rfl
    · rw [hsum]
      have hre := hq (fun g => if h : g ∈ Y then x ⟨g, h⟩ else 0)
      rw [hqf] at hre
      have hc : ∀ i : Y, (if h : (i : γ) ∈ Y then x ⟨i, h⟩ else 0) = x i := fun i => by simp
      simp only [hc] at hre
      have him : (∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        simp only [map_sum, map_mul, Complex.conj_conj]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hh i i.2 j j.2, Complex.conj_conj]
        ring
      exact Complex.le_def.mpr ⟨by simpa using hre, by rw [Complex.zero_im, him]⟩

theorem block_quad {a : α → α → ℂ} {w : α → β → ℂ} {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b)
    (c : α → ℂ) (d : β → ℂ) :
    0 ≤ (qf Y₁ a c).re + (qf Y₂ b d).re + 2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c p) * w p q * d q).re := by
  have h1 := ((psd_iff_qf _ _).1 ((blockPSD_iff Y₁ Y₂ a w b).1 h)).2 (Sum.elim c d)
  rw [qf_block] at h1
  simpa using h1

end block

theorem cross_le {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ^ 2 ≤ A * B) (hx : 0 ≤ x) : 2 * x ≤ A + B := by
  have hAB : 0 ≤ A + B := by linarith
  by_contra hc
  push_neg at hc
  nlinarith [sq_nonneg (A - B), mul_nonneg hAB hx]

theorem block_of_cauchy_schwarz : KB.BlockOfCS := by
  intro α β Y₁ Y₂ a w b ha hb hcs
  have ha' := (psd_iff_qf Y₁ a).1 ha
  have hb' := (psd_iff_qf Y₂ b).1 hb
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rcases x with p | q <;> rcases y with p' | q'
    · simpa [blockK] using ha'.1 p (by simpa using hx) p' (by simpa using hy)
    · simp [blockK]
    · simp [blockK]
    · simpa [blockK] using hb'.1 q (by simpa using hx) q' (by simpa using hy)
  · rw [qf_block]
    set X := ∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q) with hX
    have hA := ha'.2 (fun p => c (.inl p))
    have hB := hb'.2 (fun q => c (.inr q))
    have h1 := hcs (fun p => conj (c (.inl p))) (fun q => conj (c (.inr q)))
    have eX : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * conj (conj (c (.inr q))) * w p q) = X := by
      rw [hX]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.conj_conj]
      ring
    have eA : (∑ p ∈ Y₁, ∑ p' ∈ Y₁, conj (c (.inl p)) * conj (conj (c (.inl p'))) * a p p') =
        qf Y₁ a (fun p => c (.inl p)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have eB : (∑ q ∈ Y₂, ∑ q' ∈ Y₂, conj (c (.inr q)) * conj (conj (c (.inr q'))) * b q q') =
        qf Y₂ b (fun q => c (.inr q)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eX, eA, eB] at h1
    have hx := cross_le hA hB h1 (norm_nonneg X)
    have hre : -‖X‖ ≤ X.re := by
      have h2 := Complex.normSq_eq_norm_sq X
      rw [Complex.normSq_apply] at h2
      nlinarith [sq_nonneg X.im, norm_nonneg X]
    linarith

theorem blockPSD_mul {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a a' : α → α → ℂ} {w w' : α → β → ℂ}
    {b b' : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) (h' : KB.BlockPSD Y₁ Y₂ a' w' b') :
    KB.BlockPSD Y₁ Y₂ (fun p q => a p q * a' p q) (fun p q => w p q * w' p q) (fun p q => b p q * b' p q) := by
  rw [blockPSD_iff] at *
  refine Jx7.psd_congr ?_ (Jx7.psd_mul h h')
  intro x _ y _
  rcases x with p | q <;> rcases y with p' | q' <;> simp [blockK, map_mul]

theorem blockPSD_ones {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) :
    KB.BlockPSD Y₁ Y₂ (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) := by
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x _ y _ => ?_, fun c => ?_⟩
  · cases x <;> cases y <;> simp [blockK]
  · have hq : qf (Y₁.disjSum Y₂) (blockK (fun _ _ => (1 : ℂ)) (fun _ _ => 1) (fun _ _ => 1)) c =
        conj (∑ x ∈ Y₁.disjSum Y₂, c x) * ∑ x ∈ Y₁.disjSum Y₂, c x := by
      unfold qf
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> simp [blockK]
    rw [hq, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]

theorem blockPSD_prod {α β ι : Type} {Y₁ : Finset α} {Y₂ : Finset β} (s : Finset ι) (a : ι → α → α → ℂ)
    (w : ι → α → β → ℂ) (b : ι → β → β → ℂ) (h : ∀ v ∈ s, KB.BlockPSD Y₁ Y₂ (a v) (w v) (b v)) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ∏ v ∈ s, a v p q) (fun p q => ∏ v ∈ s, w v p q)
      (fun p q => ∏ v ∈ s, b v p q) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using blockPSD_ones Y₁ Y₂
  · intro v t hv ih h
    simp only [Finset.prod_insert hv]
    exact blockPSD_mul (h v (Finset.mem_insert_self v t)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem block_cross_le {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a : α → α → ℂ} {w : α → β → ℂ}
    {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) :
    ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q‖ ≤ ((∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re + (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re) / 2 := by
  have key : ∀ u v : ℂ, 0 ≤ Complex.normSq u * (∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re +
      Complex.normSq v * (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re +
      2 * (conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q).re := by
    intro u v
    have h1 := block_quad Y₁ Y₂ h (fun _ => u) (fun _ => v)
    have e1 : qf Y₁ a (fun _ => u) = conj u * u * ∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e2 : qf Y₂ b (fun _ => v) = conj v * v * ∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e3 : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj u * w p q * v) = conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [e1, e2, e3, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h1
    exact h1
  set S := ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q with hS
  by_cases h0 : S = 0
  · have k1 := key 1 (-1)
    rw [h0] at k1
    simp at k1
    rw [h0, norm_zero]
    simp only [Complex.re_sum]
    linarith
  · have hn : 0 < ‖S‖ := norm_pos_iff.mpr h0
    have k2 := key S (-(‖S‖ : ℂ))
    have hns : Complex.normSq S = ‖S‖ ^ 2 := Complex.normSq_eq_norm_sq S
    have hnr : Complex.normSq (-(‖S‖ : ℂ)) = ‖S‖ ^ 2 := by
      rw [Complex.normSq_neg, Complex.normSq_ofReal]
      ring
    have hcr : (conj S * -(‖S‖ : ℂ) * S).re = -(‖S‖ ^ 3) := by
      have e : conj S * -(‖S‖ : ℂ) * S = -((‖S‖ : ℂ) * (Complex.normSq S : ℂ)) := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      rw [e, hns, Complex.neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      ring
    rw [hns, hnr, hcr] at k2
    nlinarith [mul_pos hn hn, k2]

theorem blockSchur_true : KB.BlockSchur := by
  intro ι α β _ Y₁ Y₂ κa κw κb a w b hκ hv
  exact block_cross_le (blockPSD_mul hκ (blockPSD_prod Finset.univ a w b (fun v _ => hv v)))

end Formalism.FourierDecayAlt.P.PBA
