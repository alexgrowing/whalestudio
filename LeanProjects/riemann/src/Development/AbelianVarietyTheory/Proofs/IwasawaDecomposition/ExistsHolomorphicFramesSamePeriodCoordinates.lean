import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

namespace GlobalTheory.HolFrameLift

open ReciprocityTheory.ChartRestriction.G.FD

section Mat

variable {r : ℕ} (p : Fin r → Prop) [DecidablePred p]

def mixCol (A P : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k a => if p a then A k a else P k a

def mixRow (A P : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => if p a then (1 : Matrix (Fin r) (Fin r) ℂ) a j else (A⁻¹ * mixCol p A P) a j

variable {A P : Matrix (Fin r) (Fin r) ℂ}

theorem inv_mul_mixCol (hA : A.det ≠ 0) {j : Fin r} (hj : p j) (i : Fin r) :
    (A⁻¹ * mixCol p A P) i j = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
  have h : (A⁻¹ * mixCol p A P) i j = (A⁻¹ * A) i j := by
    simp only [Matrix.mul_apply, mixCol, Matrix.of_apply, if_pos hj]
  rw [h, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)]

theorem det_mixRow_ne_zero (hA : A.det ≠ 0) (hQ : (mixCol p A P).det ≠ 0) : (mixRow p A P).det ≠ 0 := by
  have hM : (A⁻¹ * mixCol p A P).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (inv_ne_zero hA) hQ
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hS : ∀ a, p a → v a = 0 := by
    intro a ha
    have e : (mixRow p A P *ᵥ v) a = ((1 : Matrix (Fin r) (Fin r) ℂ) *ᵥ v) a := by
      simp only [Matrix.mulVec, dotProduct, mixRow, Matrix.of_apply, if_pos ha]
    rw [Matrix.one_mulVec, hv] at e
    exact e.symm
  have hT : ∀ a, ¬ p a → ((A⁻¹ * mixCol p A P) *ᵥ v) a = 0 := by
    intro a ha
    have e : (mixRow p A P *ᵥ v) a = ((A⁻¹ * mixCol p A P) *ᵥ v) a := by
      simp only [Matrix.mulVec, dotProduct, mixRow, Matrix.of_apply, if_neg ha]
    rw [← e, hv]
    rfl
  have hfix : ∀ w : Fin r → ℂ, (∀ b, ¬ p b → w b = 0) → (A⁻¹ * mixCol p A P) *ᵥ w = w := by
    intro w hw
    funext i
    have e : ((A⁻¹ * mixCol p A P) *ᵥ w) i = ((1 : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : p b
      · rw [inv_mul_mixCol p hA hb i]
      · rw [hw b hb, mul_zero, mul_zero]
    rw [e, Matrix.one_mulVec]
  have heq : v = (A⁻¹ * mixCol p A P) *ᵥ v := by
    have h2 := hfix _ hT
    have h3 : (A⁻¹ * mixCol p A P) *ᵥ (v - (A⁻¹ * mixCol p A P) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_sub, h2, sub_self]
    exact (sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hM h3))
  apply hv0
  funext a
  by_cases ha : p a
  · exact hS a ha
  · rw [heq]
    exact hT a ha

private theorem mix_apply_eq_one_apply_of_mem (hA : A.det ≠ 0) {j : Fin r} (hj : p j) (a : Fin r) :
    mixRow p A P a j = (1 : Matrix (Fin r) (Fin r) ℂ) a j := by
  by_cases ha : p a
  · simp only [mixRow, Matrix.of_apply, if_pos ha]
  · simp only [mixRow, Matrix.of_apply, if_neg ha]
    exact inv_mul_mixCol p hA hj a

theorem mix_col_eq (hA : A.det ≠ 0) (hQ : (mixCol p A P).det ≠ 0) {j : Fin r} (hj : p j) (k : Fin r) :
    (mixCol p A P * (mixRow p A P)⁻¹) k j = A k j := by
  have hR := det_mixRow_ne_zero p hA hQ
  have hcol : ∀ a, (mixRow p A P)⁻¹ a j = (1 : Matrix (Fin r) (Fin r) ℂ) a j := by
    intro a
    have h1 : ((mixRow p A P)⁻¹ * mixRow p A P) a j = (1 : Matrix (Fin r) (Fin r) ℂ) a j := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hR)]
    rw [← h1, Matrix.mul_apply]
    simp [mix_apply_eq_one_apply_of_mem p hA hj, Matrix.one_apply]
  rw [Matrix.mul_apply]
  simp [hcol, Matrix.one_apply, mixCol, hj]

theorem mix_inv_row_eq (hA : A.det ≠ 0) (hQ : (mixCol p A P).det ≠ 0) {a : Fin r} (ha : ¬ p a) (k : Fin r) :
    (mixCol p A P * (mixRow p A P)⁻¹)⁻¹ a k = A⁻¹ a k := by
  have hR := det_mixRow_ne_zero p hA hQ
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hR)]
  have e : (mixRow p A P * (mixCol p A P)⁻¹) a k = (A⁻¹ * mixCol p A P * (mixCol p A P)⁻¹) a k := by
    simp only [Matrix.mul_apply, mixRow, Matrix.of_apply, if_neg ha]
  rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQ), Matrix.mul_one]

theorem differentiableOn_det {B : Set ℂ} {M : ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hM : ∀ i j, DifferentiableOn ℂ (fun w => M w i j) B) :
    DifferentiableOn ℂ (fun w => (M w).det) B := by
  simp only [Matrix.det_apply']
  exact DifferentiableOn.fun_sum fun σ _ => (differentiableOn_const _).mul
    (DifferentiableOn.fun_finsetProd fun i _ => hM _ _)

theorem differentiableOn_inv {B : Set ℂ} {M : ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hM : ∀ i j, DifferentiableOn ℂ (fun w => M w i j) B) (hd : ∀ w ∈ B, (M w).det ≠ 0) (i j : Fin r) :
    DifferentiableOn ℂ (fun w => (M w)⁻¹ i j) B := by
  have hadj : DifferentiableOn ℂ (fun w => (M w).adjugate i j) B := by
    simp only [Matrix.adjugate_apply]
    apply differentiableOn_det
    intro k l
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hk]
      exact hM k l
  have e : (fun w => (M w)⁻¹ i j) = fun w => ((M w).det)⁻¹ * (M w).adjugate i j := by
    funext w
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [e]
  exact ((differentiableOn_det hM).inv hd).mul hadj

theorem differentiableOn_mix {B : Set ℂ} {A : ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hA : ∀ w ∈ B, (A w).det ≠ 0) (hQ : ∀ w ∈ B, (mixCol p (A w) P).det ≠ 0)
    (hc : ∀ a, p a → ∀ k, DifferentiableOn ℂ (fun w => A w k a) B)
    (hr : ∀ a, ¬ p a → ∀ k, DifferentiableOn ℂ (fun w => (A w)⁻¹ a k) B) (i j : Fin r) :
    DifferentiableOn ℂ (fun w => (mixCol p (A w) P * (mixRow p (A w) P)⁻¹) i j) B := by
  have hQd : ∀ k l, DifferentiableOn ℂ (fun w => mixCol p (A w) P k l) B := by
    intro k l
    by_cases hl : p l
    · simp only [mixCol, Matrix.of_apply, if_pos hl]
      exact hc l hl k
    · simp only [mixCol, Matrix.of_apply, if_neg hl]
      exact differentiableOn_const _
  have hRd : ∀ k l, DifferentiableOn ℂ (fun w => mixRow p (A w) P k l) B := by
    intro k l
    by_cases hk : p k
    · simp only [mixRow, Matrix.of_apply, if_pos hk]
      exact differentiableOn_const _
    · simp only [mixRow, Matrix.of_apply, if_neg hk, Matrix.mul_apply]
      exact DifferentiableOn.fun_sum fun m _ => (hr k hk m).mul (hQd m l)
  have hRi := differentiableOn_inv (M := fun w => mixRow p (A w) P) hRd
    (fun w hw => det_mixRow_ne_zero p (hA w hw) (hQ w hw))
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun m _ => (hQd i m).mul (hRi m j)

end Mat

theorem differentiableOn_of_span {E : Type} [Field E] {r : ℕ} {B : Set ℂ}
    (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ : ℂ → (Fin r → E) → ℂ) (ha : ∀ n v w, Φ n (v + w) = Φ n v + Φ n w)
    (hs : ∀ n (c : E) v, Φ n (c • v) = σ c * Φ n v) (hσ : σ 0 = 0)
    (h : ∀ v ∈ S, DifferentiableOn ℂ (fun n => Φ n v) B) (v : Fin r → E) :
    DifferentiableOn ℂ (fun n => Φ n v) B := by
  have h0 : ∀ n, Φ n 0 = 0 := fun n => by
    have e := hs n 0 0
    rwa [zero_smul, hσ, zero_mul] at e
  have hv : v ∈ Submodule.span E S := by
    rw [hS]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    simp only [h0]
    exact differentiableOn_const 0
  | add x y _ _ hx hy =>
    simp only [ha]
    exact hx.add hy
  | smul c x _ hx =>
    simp only [hs]
    exact (differentiableOn_const (σ c)).mul hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem det_mixCol_ne_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {P : Matrix (Fin r) (Fin r) ℂ}
    (hP : gram τ.1 X.Gm P = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) :
    (mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat x τ) P).det ≠ 0 := by
  have sum_castLE : ∀ (f : Fin r → Fin r → ℂ) (v : Fin r → ℂ),
      ∑ a : Fin X.p0, v (Fin.castLE X.p0_le a) • f (Fin.castLE X.p0_le a) =
        ∑ i : Fin r, (if (i : ℕ) < X.p0 then v i else 0) • f i := by
    intro f v
    refine Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective X.p0_le) _
      (fun i : Fin r => (if (i : ℕ) < X.p0 then v i else 0) • f i) ?_ ?_
    · intro i hi
      have hlt : ¬ (i : ℕ) < X.p0 := fun hlt => hi ⟨⟨i, hlt⟩, Fin.ext rfl⟩
      simp [hlt]
    · intro a
      simp [a.isLt]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin r → ℂ, γ = fun i : Fin r => if (i : ℕ) < X.p0 then 0 else v i := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin X.p0 → ℂ, c = fun a => v (Fin.castLE X.p0_le a) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin r → ℂ, U = ∑ a, c a • X.colP x τ a := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Fin r → ℂ, W = ∑ i, γ i • col P i := ⟨_, rfl⟩
  have hUW : U + W = 0 := by
    rw [← hv, Data.mulVec_eq_sum_col, hU, hW, hc, hγ]
    simp only [Data.colP]
    rw [sum_castLE (col (mat x τ)) v, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < X.p0
    · funext k
      simp [hi, col, mixCol]
    · funext k
      simp [hi, col, mixCol]
  have hW' : W = (-1 : ℂ) • U := by
    rw [neg_one_smul]
    exact add_eq_zero_iff_eq_neg.mp ((add_comm W U).trans hUW)
  have hpos := Data.gramPos_posDef X hx τ
  have hUU : hermC τ.1 X.Gm U U = ∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b) := by
    rw [hU, hermC_quad]
    simp only [Data.gramPos_apply]
  have hg : ∀ a b, hermC τ.1 X.Gm (col P a) (col P b) =
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) a b := by
    intro a b
    rw [← hP]
    rfl
  have hWW : (hermC τ.1 X.Gm W W).re = -∑ i, Complex.normSq (γ i) := by
    rw [hW, hermC_quad]
    simp only [hg, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < X.p0
    · simp [hγ, hi]
    · simp [hγ, hi, sgn, Complex.mul_conj]
  have hsame : hermC τ.1 X.Gm W W = hermC τ.1 X.Gm U U := by
    rw [hW', hermC_smul_left, hermC_smul_right]
    simp
  have hUre : 0 ≤ (hermC τ.1 X.Gm U U).re := by
    rw [hUU]
    exact quad_re_nonneg hpos.posSemidef c
  have hsq : 0 ≤ ∑ i, Complex.normSq (γ i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hγ0 : ∑ i, Complex.normSq (γ i) = 0 := by
    rw [hsame] at hWW
    linarith
  have hU0 : (hermC τ.1 X.Gm U U).re = 0 := by
    rw [← hsame, hWW, hγ0, neg_zero]
  have hc0 : c = 0 := by
    by_contra hne
    have h1 := quad_re_pos hpos hne
    rw [← hUU, hU0] at h1
    exact lt_irrefl _ h1
  apply hv0
  funext i
  by_cases hi : (i : ℕ) < X.p0
  · have h1 := congrFun hc0 ⟨i, hi⟩
    rw [hc] at h1
    simpa using h1
  · have h1 : Complex.normSq (γ i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (γ j))).mp hγ0 i
        (Finset.mem_univ _)
    rw [Complex.normSq_eq_zero, hγ] at h1
    simpa [hi] using h1

theorem mem_dom_of_eq {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : ∀ τ, (mat y τ).det ≠ 0)
    (hc : ∀ τ, ∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k, mat y τ k a = mat x τ k a)
    (hr : ∀ τ, ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k, (mat y τ)⁻¹ a k = (mat x τ)⁻¹ a k) :
    y ∈ X.dom := by
  have hxd : ∀ τ, (mat x τ).det ≠ 0 := fun τ => ((Data.mem_dom_iff X x).mp hx τ).1
  have hb : (fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ)) ∈ Bor X.Ψ r := by
    simp only [Bor, Set.mem_setOf_eq]
    intro τ
    refine ⟨?_, ?_⟩
    · show ((mat x τ)⁻¹ * mat y τ).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact mul_ne_zero (inv_ne_zero (hxd τ)) (hy τ)
    · intro a c hca
      show ((mat x τ)⁻¹ * mat y τ) a c = 0
      by_cases hc' : (c : ℕ) < X.p0
      · have e : ((mat x τ)⁻¹ * mat y τ) a c = ((mat x τ)⁻¹ * mat x τ) a c := by
          simp only [Matrix.mul_apply, hc τ c hc']
        rw [e, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hxd τ)),
          Matrix.one_apply_ne (ne_of_gt hca)]
      · have ha' : ¬ (a : ℕ) < X.p0 := fun h => hc' (lt_trans (show (c : ℕ) < a from hca) h)
        have e : ((mat x τ)⁻¹ * mat y τ) a c = ((mat y τ)⁻¹ * mat y τ) a c := by
          simp only [Matrix.mul_apply, ← hr τ a ha']
        rw [e, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hy τ)),
          Matrix.one_apply_ne (ne_of_gt hca)]
  have hyb : y = rmul x (fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ)) := by
    funext τ
    have h1 : mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ :=
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hxd τ))
    exact h1.symm
  rw [hyb]
  exact OrthogonalFrameDomain.rmul_mem_dom X hx hb

theorem exists_holomorphic_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (B : Set ℂ) (x₁ : ℂ → Frame X.Ψ r), (∀ w ∈ B, x₁ w ∈ X.dom) → (∀ v ∈ X.Λ, ∀ τ a, DifferentiableOn ℂ (fun w => GlobalTheory.GenericFrames.pc X (x₁ w) v τ a) B) → ∃ x : ℂ → Frame X.Ψ r, DifferentiableOn ℂ x B ∧ ∀ w ∈ B, x w ∈ X.dom ∧ ∀ v τ a, GlobalTheory.GenericFrames.pc X (x w) v τ a = GlobalTheory.GenericFrames.pc X (x₁ w) v τ a := by
  intro E _ _ _ r X B x₁ hdom hdiff
  have hemb_add : ∀ (τ : E →+* ℂ) (v v' : Fin r → E),
      Data.emb τ (v + v') = Data.emb τ v + Data.emb τ v' := by
    intro τ v v'
    funext k
    simp [Data.emb]
  have hemb_smul : ∀ (τ : E →+* ℂ) (c : E) (v : Fin r → E),
      Data.emb τ (c • v) = τ c • Data.emb τ v := by
    intro τ c v
    funext k
    simp [Data.emb]
  have hall : ∀ v τ a, DifferentiableOn ℂ (fun w => GlobalTheory.GenericFrames.pc X (x₁ w) v τ a) B := by
    intro v τ a
    by_cases ha : (a : ℕ) < X.p0
    · have key := differentiableOn_of_span (B := B) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => conj (τ.1 c))
        (fun w v => hermC τ.1 X.Gm (col (mat (x₁ w) τ) a) (Data.emb τ.1 v))
        (fun w v v' => by simp only [hemb_add, hermC_add_right])
        (fun w c v => by simp only [hemb_smul, hermC_smul_right])
        (by simp)
        (fun v hv => by simpa [GlobalTheory.GenericFrames.pc, ha] using hdiff v hv τ a) v
      simpa [GlobalTheory.GenericFrames.pc, ha] using key
    · have key := differentiableOn_of_span (B := B) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun w v => ((mat (x₁ w) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun w v v' => by simp only [hemb_add, Matrix.mulVec_add, Pi.add_apply])
        (fun w c v => by simp only [hemb_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul])
        (by simp)
        (fun v hv => by simpa [GlobalTheory.GenericFrames.pc, ha] using hdiff v hv τ a) v
      simpa [GlobalTheory.GenericFrames.pc, ha] using key
  have hcolD : ∀ τ : X.Ψ, ∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k,
      DifferentiableOn ℂ (fun w => mat (x₁ w) τ k a) B := by
    intro τ a ha k
    have h := hall (fun b => cc (X.Gm⁻¹ b k)) τ a
    simp only [GlobalTheory.GenericFrames.pc, if_pos ha,
      GlobalTheory.PeriodLift.hermC_emb_inv_col τ.1 X.Gm X.Gm_det] at h
    exact h
  have hrowD : ∀ τ : X.Ψ, ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k,
      DifferentiableOn ℂ (fun w => (mat (x₁ w) τ)⁻¹ a k) B := by
    intro τ a ha k
    have he : Data.emb τ.1 (Pi.single k (1 : E)) = Pi.single k 1 := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [Data.emb]
      · simp [Data.emb, hj]
    have hv : ∀ w, GlobalTheory.GenericFrames.pc X (x₁ w) (Pi.single k 1) τ a = (mat (x₁ w) τ)⁻¹ a k := by
      intro w
      simp only [GlobalTheory.GenericFrames.pc, if_neg ha, he]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have h := hall (Pi.single k 1) τ a
    simpa only [hv] using h
  choose P hPdet hP using X.signature
  have hdetA : ∀ w ∈ B, ∀ τ, (mat (x₁ w) τ).det ≠ 0 :=
    fun w hw τ => ((Data.mem_dom_iff X _).mp (hdom w hw) τ).1
  have hdetQ : ∀ w ∈ B, ∀ τ,
      (mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ)).det ≠ 0 :=
    fun w hw τ => det_mixCol_ne_zero X (hdom w hw) τ (hP τ)
  refine ⟨fun w τ => mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
      (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹, ?_, ?_⟩
  · refine differentiableOn_pi.mpr fun τ => differentiableOn_pi.mpr fun i =>
      differentiableOn_pi.mpr fun j => ?_
    exact differentiableOn_mix (fun a : Fin r => (a : ℕ) < X.p0) (P := P τ)
      (A := fun w => mat (x₁ w) τ) (fun w hw => hdetA w hw τ) (fun w hw => hdetQ w hw τ)
      (hcolD τ) (hrowD τ) i j
  · intro w hw
    have hmat : ∀ τ, mat ((fun w τ => mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
        (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹ : ℂ → Frame X.Ψ r) w) τ =
        mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
        (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹ := fun τ => rfl
    have hcolEq : ∀ τ, ∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k,
        mat ((fun w τ => mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
        (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹ : ℂ → Frame X.Ψ r) w) τ k a =
          mat (x₁ w) τ k a := by
      intro τ a ha k
      rw [hmat]
      exact mix_col_eq (fun a : Fin r => (a : ℕ) < X.p0) (hdetA w hw τ) (hdetQ w hw τ) ha k
    have hrowEq : ∀ τ, ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k,
        (mat ((fun w τ => mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
        (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹ : ℂ → Frame X.Ψ r) w) τ)⁻¹ a k =
          (mat (x₁ w) τ)⁻¹ a k := by
      intro τ a ha k
      rw [hmat]
      exact mix_inv_row_eq (fun a : Fin r => (a : ℕ) < X.p0) (hdetA w hw τ) (hdetQ w hw τ) ha k
    have hydet : ∀ τ, (mat ((fun w τ => mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
        (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹ : ℂ → Frame X.Ψ r) w) τ).det ≠ 0 := by
      intro τ
      rw [hmat, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact mul_ne_zero (hdetQ w hw τ)
        (inv_ne_zero (det_mixRow_ne_zero _ (hdetA w hw τ) (hdetQ w hw τ)))
    refine ⟨mem_dom_of_eq X (hdom w hw) hydet hcolEq hrowEq, ?_⟩
    intro v τ a
    by_cases ha : (a : ℕ) < X.p0
    · have hcol : col (mat ((fun w τ => mixCol (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ) *
          (mixRow (fun a : Fin r => (a : ℕ) < X.p0) (mat (x₁ w) τ) (P τ))⁻¹ : ℂ → Frame X.Ψ r) w) τ) a =
          col (mat (x₁ w) τ) a := by
        funext k
        exact hcolEq τ a ha k
      simp only [GlobalTheory.GenericFrames.pc, if_pos ha]
      rw [hcol]
    · simp only [GlobalTheory.GenericFrames.pc, if_neg ha, Matrix.mulVec, dotProduct, hrowEq τ a ha]

end GlobalTheory.HolFrameLift
