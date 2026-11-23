import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

lemma nf_norm_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] {n : ℕ} (x : Fin n → E) :
    ‖∑ i, x i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  have h1 : ‖∑ i, x i‖ ≤ ∑ i, ‖x i‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => ‖x i‖)
  calc ‖∑ i, x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa using h2

lemma nf_globCoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {Θ : B.DiffOp k r Wp Wq} {d d' : ℝ}
    (h : CutMP.GlobCoef Θ d) (hd : d ≤ d') : CutMP.GlobCoef Θ d' := by
  intro Tm hTm
  obtain ⟨h1, h2, h3⟩ := h Tm hTm
  refine ⟨h1, h2, fun m => ?_⟩
  obtain ⟨Cb, hCb⟩ := h3 m
  refine ⟨max Cb 0, fun u w hu hw hl g hg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hp : B.gN g ^ d ≤ B.gN g ^ d' := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hp0 : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (by linarith) _
  obtain ⟨a1, a2⟩ := hCb u w hu hw hl g hg
  constructor
  · calc _ ≤ Cb * B.gN g ^ d := a1
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ d' := mul_le_mul_of_nonneg_left hp (le_max_right _ _)
  · calc _ ≤ Cb * B.gN g ^ d := a2
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ d' := mul_le_mul_of_nonneg_left hp (le_max_right _ _)

lemma nfOpOK_mono {C C' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {N : ℕ} {Th : B.DiffOp P.k P.r Wp Wq} (h : NFOpOK C p N Th) (hC : C ≤ C') :
    NFOpOK C' p N Th := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hn : 0 ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; positivity
  refine ⟨h1, h2, nf_globCoef_mono h3 ?_, le_trans h4 ?_⟩
  · have : 0 ≤ ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
    have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) =
        x * (((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) := fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hC this
  · have : 0 ≤ CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
    have e : ∀ x : ℝ, x * CutMP.nDim P.k P.r * ((N : ℝ) + 1) = x * (CutMP.nDim P.k P.r * ((N : ℝ) + 1)) :=
      fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hC this

lemma nf_empty_bound (hV : NFVMul) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ N : ℕ) (hNp : N ≤ 2 * p₀) (χ : ℝ → ℝ) (K : ℝ)
    (Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq)
    (hap : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g)
    (ε : ℝ) (c : Fin (P.r + 1) → ℂ) (hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1))
    (hG : 0 < TBB.Gp p (TBB.bigPt P.r c)) (hK : |χ (TBB.Gp p (TBB.bigPt P.r c) / ε)| ≤ K) :
    ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) [] c‖ ≤
      K ^ 2 * ∑ t : Fin 2, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply (![Th₀, Th₁] t) f) (P.r + 1) [] (TBB.bigPt P.r c) := by
  set γ := TBB.bigPt P.r c with hγ
  have hH : D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      fun g => (((fun y => χ (y / ε) * y ^ p₀) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g := by
    funext g
    simp only [D.cutF, TBBx4.fpm, ContinuousLinearMap.comp_id, smul_smul, Complex.ofReal_mul, Complex.ofReal_pow]
  have h0 : B.opApply Th₀ f = f := funext fun g => (hap f g).1
  have h1 : B.opApply Th₁ f = fun g => (((fun y : ℝ => y ^ N) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g :=
    funext fun g => (hap f g).2
  show ‖TBB.Ew p (fun _ => 1) _ (P.r + 1) [] γ‖ ≤ _
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hH, h0, h1, TBBx2.Tri.Ew_top p _ hl, TBBx2.Tri.Ew_top p _ hl, TBBx2.Tri.Ew_top p _ hl,
    hV Wp Wq P p (fun y => χ (y / ε) * y ^ p₀) f γ hl hG, hV Wp Wq P p (fun y : ℝ => y ^ N) f γ hl hG, TBBx4.hsVec_real_smul_sq, TBBx4.hsVec_real_smul_sq]
  set G := TBB.Gp p γ
  set S := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)
  set v := ‖B.hsVec (p.V f γ)‖ ^ 2
  set x := χ (G / ε)
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hv : 0 ≤ v := sq_nonneg _
  have hG0 : 0 ≤ G := hG.le
  have hx2 : x ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hK 2
  have hGa : G ^ (2 * p₀) = G ^ (2 * p₀ - N) * G ^ N := by rw [← pow_add, Nat.sub_add_cancel hNp]
  have hGN : G ^ N ≤ 1 + (G ^ N) ^ 2 := by nlinarith [sq_nonneg (G ^ N - 1), pow_nonneg hG0 N]
  have hLHS : 0 ≤ S * ((x * G ^ p₀) ^ 2 * v) := by positivity
  rw [Real.norm_of_nonneg hLHS, Real.norm_of_nonneg hG0]
  have e1 : S * ((x * G ^ p₀) ^ 2 * v) = (S * v * G ^ (2 * p₀ - N)) * (x ^ 2 * G ^ N) := by
    rw [mul_pow, ← pow_mul, mul_comm p₀ 2, hGa]; ring
  have e2 : K ^ 2 * (G ^ (2 * p₀ - N) * (S * v) + G ^ (2 * p₀ - N) * (S * ((G ^ N) ^ 2 * v))) =
      (S * v * G ^ (2 * p₀ - N)) * (K ^ 2 * (1 + (G ^ N) ^ 2)) := by ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul hx2 hGN (pow_nonneg hG0 N) (sq_nonneg K)

lemma nf_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {n : ℕ} (E : Wp →L[ℂ] Wp) (a : Fin n → ℂ) (W : Fin n → (Wq →L[ℂ] Wp)) :
    E.comp (∑ q, a q • W q) = ∑ q, a q • E.comp (W q) := by
  ext v
  simp [map_sum, map_smul]

lemma nf_block {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ} (E : Wp →L[ℂ] Wp) (a : Fin n → ℝ) (Kt : ℝ)
    (ha : ∀ q, |a q| ≤ Kt) (W : Fin n → (Wq →L[ℂ] Wp)) (d : ℝ) :
    d ^ 2 * ‖B.hsVec (E.comp (∑ q, ((a q : ℝ) : ℂ) • W q))‖ ^ 2 ≤
      (n : ℝ) * Kt ^ 2 * ∑ q, d ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
  rw [nf_comp_sum, TBBx2.Tri.hsVec_sum]
  simp only [TBBx2.Tri.hsVec_smul]
  have h1 := nf_norm_sum_sq_le (fun q => ((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q)))
  have h2 : ∀ q, ‖((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2 ≤ Kt ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
    intro q
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have : |a q| ^ 2 ≤ Kt ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (ha q) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h3 : ∑ q, ‖((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2 ≤ Kt ^ 2 * ∑ q, ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun q _ => h2 q
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc d ^ 2 * ‖∑ q, ((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2
      ≤ d ^ 2 * ((n : ℝ) * (Kt ^ 2 * ∑ q, ‖B.hsVec (E.comp (W q))‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 hn)) (sq_nonneg d)
    _ = (n : ℝ) * Kt ^ 2 * ∑ q, d ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring

end

end Formalism.FourierDecayAlt.P.CutBP
