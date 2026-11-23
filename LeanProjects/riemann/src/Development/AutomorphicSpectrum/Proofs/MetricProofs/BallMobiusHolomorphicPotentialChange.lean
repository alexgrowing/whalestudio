import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem posDef_one_sub_swap (M : Matrix a b ℂ) (h : (1 - Mᴴ * M).PosDef) : (1 - M * Mᴴ).PosDef := by
  set K := (1 - Mᴴ * M)⁻¹ with hK
  have hKp : K.PosDef := h.inv
  have hu : IsUnit (1 - Mᴴ * M).det := (h.det_pos.ne').isUnit
  have hNK : (1 - Mᴴ * M) * K = 1 := Matrix.mul_nonsing_inv _ hu
  have hX : (1 + M * K * Mᴴ).PosDef :=
    Matrix.PosDef.one.add_posSemidef (hKp.posSemidef.mul_mul_conjTranspose_same M)
  have h1 : K = 1 + Mᴴ * M * K := by
    rw [sub_mul, one_mul] at hNK
    rw [← hNK]; abel
  have h2 : M * K * Mᴴ = M * Mᴴ + M * Mᴴ * (M * K * Mᴴ) := by
    conv_lhs => rw [h1]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hmul : (1 - M * Mᴴ) * (1 + M * K * Mᴴ) = 1 := by
    generalize M * K * Mᴴ = X at h2
    generalize M * Mᴴ = Y at h2
    have e : (1 - Y) * (1 + X) = 1 + (X - (Y + Y * X)) := by noncomm_ring
    rw [e, ← h2]; simp
  have : 1 - M * Mᴴ = (1 + M * K * Mᴴ)⁻¹ := (Matrix.inv_eq_left_inv hmul).symm
  rw [this]; exact hX.inv

theorem transpose_one_sub (Y : Matrix a b ℂ) : (1 - Yᴴ * Y)ᵀ = 1 - Yᵀ * (Yᵀ)ᴴ := by
  simp [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map]

theorem posDef_transpose_iff (Z : Matrix a b ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ (1 - (Zᵀ)ᴴ * Zᵀ).PosDef := by
  constructor
  · intro h
    have h1 := h.transpose
    rw [transpose_one_sub] at h1
    have h2 := posDef_one_sub_swap (Zᵀ)ᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)
    rwa [Matrix.conjTranspose_conjTranspose] at h2
  · intro h
    have h2 := posDef_one_sub_swap Zᵀ h
    rw [← transpose_one_sub] at h2
    have h1 := h2.transpose
    rwa [Matrix.transpose_transpose] at h1

theorem det_transpose_eq (Z : Matrix a b ℂ) :
    (1 - Zᴴ * Z).det = (1 - (Zᵀ)ᴴ * Zᵀ).det := by
  rw [← Matrix.det_transpose, transpose_one_sub, Matrix.det_one_sub_mul_comm]

section Act
variable {j j' : ℕ}

def den (u : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  u.toBlocks₁₁ + u.toBlocks₁₂ * W

def num (u : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ) : Matrix (Fin j') (Fin j) ℂ :=
  u.toBlocks₂₁ + u.toBlocks₂₂ * W

theorem den_gram {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (W : Matrix (Fin j') (Fin j) ℂ) :
    (den u W)ᴴ * den u W - (num u W)ᴴ * num u W = 1 - Wᴴ * W := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, u = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  simp only [IsSgU, sgI, fromBlocks_conjTranspose, fromBlocks_multiply] at hu
  have h := Matrix.fromBlocks_inj.1 hu
  obtain ⟨h11, h12, h21, h22⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at h11 h12 h21 h22
  simp only [den, num, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  have e : (A + B * W)ᴴ * (A + B * W) - (C + D * W)ᴴ * (C + D * W) =
      (Aᴴ * A - Cᴴ * C) + (Aᴴ * B - Cᴴ * D) * W + Wᴴ * (Bᴴ * A - Dᴴ * C) + Wᴴ * (Bᴴ * B - Dᴴ * D) * W := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have g11 : Aᴴ * A - Cᴴ * C = 1 := by rw [sub_eq_add_neg]; exact h11
  have g12 : Aᴴ * B - Cᴴ * D = 0 := by rw [sub_eq_add_neg]; exact h12
  have g21 : Bᴴ * A - Dᴴ * C = 0 := by rw [sub_eq_add_neg]; exact h21
  have g22 : Bᴴ * B - Dᴴ * D = -1 := by rw [sub_eq_add_neg]; exact h22
  rw [e, g11, g12, g21, g22]
  simp [sub_eq_add_neg]

theorem den_det_ne {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - Wᴴ * W).PosDef) : (den u W).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 := hW.dotProduct_mulVec_pos hv
  rw [← den_gram hu W, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv,
    Matrix.mulVec_zero, zero_sub, dotProduct_neg, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star] at h1
  have h2 : 0 ≤ star (num u W *ᵥ v) ⬝ᵥ (num u W *ᵥ v) := dotProduct_star_self_nonneg _
  exact lt_irrefl _ (lt_of_le_of_lt h2 (neg_pos.1 h1))

theorem moeb_gram {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - Wᴴ * W).PosDef) :
    (den u W)ᴴ * (1 - (moebW u W)ᴴ * moebW u W) * den u W = 1 - Wᴴ * W := by
  have hd := den_det_ne hu hW
  have hQ : moebW u W * den u W = num u W := by
    change num u W * (den u W)⁻¹ * den u W = _
    rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd.isUnit]
  rw [← den_gram hu W, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← hQ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem moeb_posDef {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - Wᴴ * W).PosDef) : (1 - (moebW u W)ᴴ * moebW u W).PosDef := by
  have hd := den_det_ne hu hW
  have hP : ((den u W)⁻¹)ᴴ * (1 - Wᴴ * W) * (den u W)⁻¹ = 1 - (moebW u W)ᴴ * moebW u W := by
    rw [← moeb_gram hu hW]
    have h1 : ((den u W)⁻¹)ᴴ * (den u W)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd.isUnit, Matrix.conjTranspose_one]
    have h2 : den u W * (den u W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd.isUnit
    calc _ = (((den u W)⁻¹)ᴴ * (den u W)ᴴ) * (1 - (moebW u W)ᴴ * moebW u W) * (den u W * (den u W)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  rw [← hP]
  refine hW.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hd.isUnit))

theorem moeb_det {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - Wᴴ * W).PosDef) :
    (1 - Wᴴ * W).det = ((‖(den u W).det‖ ^ 2 : ℝ) : ℂ) * (1 - (moebW u W)ᴴ * moebW u W).det := by
  rw [← moeb_gram hu hW, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have : ((‖(den u W).det‖ ^ 2 : ℝ) : ℂ) = star (den u W).det * (den u W).det := by
    rw [show star (den u W).det = (starRingEnd ℂ) (den u W).det from rfl, Complex.conj_mul']
    push_cast; rfl
  rw [this]; ring
end Act

section Conv
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem star_dot_self (y : a → ℂ) : star y ⬝ᵥ y = ((‖WithLp.toLp 2 y‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (y i) = (starRingEnd ℂ) (y i) from rfl, Complex.conj_mul']

theorem form_one_sub (Z : Matrix a b ℂ) (x : b → ℂ) :
    star x ⬝ᵥ (1 - Zᴴ * Z) *ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ x)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star, star_dot_self, star_dot_self]
  push_cast; rfl

theorem posDef_iff_norm (Z : Matrix a b ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ ∀ x : b → ℂ, x ≠ 0 → ‖WithLp.toLp 2 (Z *ᵥ x)‖ < ‖WithLp.toLp 2 x‖ := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x hx
    have h1 := h hx
    rw [form_one_sub, Complex.zero_lt_real] at h1
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (sub_pos.1 h1)
  · intro h
    refine ⟨Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self _), fun x hx => ?_⟩
    rw [form_one_sub, Complex.zero_lt_real]
    exact sub_pos.2 (pow_lt_pow_left₀ (h x hx) (norm_nonneg _) two_ne_zero)

theorem convex_ball_mat : Convex ℝ {Z : Matrix a b ℂ | (1 - Zᴴ * Z).PosDef} := by
  rw [convex_iff_forall_pos]
  intro Z₁ h₁ Z₂ h₂ s r hs hr hsr
  simp only [Set.mem_setOf_eq, posDef_iff_norm] at h₁ h₂ ⊢
  intro x hx
  have e : WithLp.toLp 2 ((s • Z₁ + r • Z₂) *ᵥ x) =
      s • WithLp.toLp 2 (Z₁ *ᵥ x) + r • WithLp.toLp 2 (Z₂ *ᵥ x) := by
    ext i
    simp [Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [e]
  calc _ ≤ ‖s • WithLp.toLp 2 (Z₁ *ᵥ x)‖ + ‖r • WithLp.toLp 2 (Z₂ *ᵥ x)‖ := norm_add_le _ _
    _ = s * ‖WithLp.toLp 2 (Z₁ *ᵥ x)‖ + r * ‖WithLp.toLp 2 (Z₂ *ᵥ x)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hr.le]
    _ < s * ‖WithLp.toLp 2 x‖ + r * ‖WithLp.toLp 2 x‖ :=
        add_lt_add (mul_lt_mul_of_pos_left (h₁ x hx) hs) (mul_lt_mul_of_pos_left (h₂ x hx) hr)
    _ = _ := by rw [← add_mul, hsr, one_mul]
end Conv

section Dom
variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem convex_ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : Convex ℝ (ballDom q) := by
  have hset : ballDom q = ⋂ τ, (fun t => ballMat q t τ) ⁻¹' {Z | (1 - Zᴴ * Z).PosDef} := by
    ext t
    simp [ballDom]
  rw [hset]
  refine convex_iInter fun τ => ?_
  let L : (Fin n → ℂ) →ₗ[ℝ] Matrix (Fin j) (Fin j') ℂ :=
    { toFun := fun t => ballMat q t τ
      map_add' := fun s t => by ext a b; simp [ballMat]
      map_smul' := fun c t => by ext a b; simp [ballMat] }
  exact convex_ball_mat.linear_preimage L

theorem zero_mem (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]; simpa using Matrix.PosDef.one

theorem ballMat_ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) (τ : Ψ) :
    ballMat q (ballPt q W) τ = (W τ)ᵀ := by
  ext a b; simp [ballMat, ballPt]

end Dom

section Hol
variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem analyticAt_det_entries {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (f : X → Matrix ι ι ℂ) (x : X)
    (h : ∀ i k, AnalyticAt ℂ (fun z => f z i k) x) : AnalyticAt ℂ (fun z => (f z).det) x := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_adjugate_entries {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (f : X → Matrix ι ι ℂ) (x : X)
    (h : ∀ i k, AnalyticAt ℂ (fun z => f z i k) x) (c d : ι) :
    AnalyticAt ℂ (fun z => (f z).adjugate c d) x := by
  simp only [Matrix.adjugate_apply]
  refine analyticAt_det_entries _ x fun i k => ?_
  by_cases hi : i = d
  · subst hi
    simpa using analyticAt_const
  · simpa [Matrix.updateRow_apply, hi] using h i k

theorem analyticAt_lin_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) {r : Type} [Fintype r] (X : Matrix r (Fin j) ℂ)
    (Y : Matrix r (Fin j') ℂ) (τ : Ψ) (t : Fin n → ℂ) (c d) :
    AnalyticAt ℂ (fun t => (X + Y * (ballMat q t τ)ᵀ) c d) t := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, ballMat, Matrix.of_apply]
  refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun e _ => analyticAt_const.mul ?_)
  exact analyticAt_pi_iff.1 analyticAt_id _

theorem analyticAt_den_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Matrix (Sg j j') (Sg j j') ℂ) (τ : Ψ)
    (t : Fin n → ℂ) (c d) : AnalyticAt ℂ (fun t => den u (ballMat q t τ)ᵀ c d) t :=
  analyticAt_lin_entry q _ _ τ t c d

theorem analyticAt_num_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Matrix (Sg j j') (Sg j j') ℂ) (τ : Ψ)
    (t : Fin n → ℂ) (c d) : AnalyticAt ℂ (fun t => num u (ballMat q t τ)ᵀ c d) t :=
  analyticAt_lin_entry q _ _ τ t c d

theorem analyticAt_moebW_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Matrix (Sg j j') (Sg j j') ℂ) (τ : Ψ)
    (t : Fin n → ℂ) (hd : (den u (ballMat q t τ)ᵀ).det ≠ 0) (c d) :
    AnalyticAt ℂ (fun t => moebW u (ballMat q t τ)ᵀ c d) t := by
  change AnalyticAt ℂ (fun t => (num u (ballMat q t τ)ᵀ * (den u (ballMat q t τ)ᵀ)⁻¹) c d) t
  simp only [Matrix.mul_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  refine Finset.analyticAt_fun_sum _ fun e _ => (analyticAt_num_entry q u τ t c e).mul
    (AnalyticAt.mul (AnalyticAt.inv (analyticAt_det_entries _ t (analyticAt_den_entry q u τ t)) hd)
      (analyticAt_adjugate_entries _ t (analyticAt_den_entry q u τ t) e d))

theorem ball_transpose {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ} (ht : t ∈ ballDom q) (τ : Ψ) :
    (1 - ((ballMat q t τ)ᵀ)ᴴ * (ballMat q t τ)ᵀ).PosDef :=
  (posDef_transpose_iff _).1 (ht τ)

theorem ballMat_moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (t : Fin n → ℂ) (τ : Ψ) : ballMat q (moebBall q u t) τ = (moebW (u τ) (ballMat q t τ)ᵀ)ᵀ :=
  ballMat_ballPt q _ τ

theorem mapsTo_moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hu : ∀ τ, IsSgU (u τ)) : Set.MapsTo (moebBall q u) (ballDom q) (ballDom q) := by
  intro t ht τ
  rw [ballMat_moebBall]
  refine (posDef_transpose_iff _).2 ?_
  rw [Matrix.transpose_transpose]
  exact moeb_posDef (hu τ) (ball_transpose ht τ)

theorem differentiableOn_moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hu : ∀ τ, IsSgU (u τ)) : DifferentiableOn ℂ (moebBall q u) (ballDom q) := by
  refine differentiableOn_pi.2 fun k t ht => ?_
  exact (analyticAt_moebW_entry q (u (q.symm k).1) (q.symm k).1 t
    (den_det_ne (hu _) (ball_transpose ht _)) _ _).differentiableAt.differentiableWithinAt

theorem log_det_moeb (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hu : ∀ τ, IsSgU (u τ)) {t : Fin n → ℂ} (ht : t ∈ ballDom q) (τ : Ψ) :
    Real.log (1 - (ballMat q (moebBall q u t) τ)ᴴ * ballMat q (moebBall q u t) τ).det.re =
      Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re -
        2 * Real.log ‖(den (u τ) (ballMat q t τ)ᵀ).det‖ := by
  have hW := ball_transpose ht τ
  have hd := den_det_ne (hu τ) hW
  have hD := moeb_det (hu τ) hW
  have hpos : 0 < (1 - (ballMat q (moebBall q u t) τ)ᴴ * ballMat q (moebBall q u t) τ).det.re :=
    (Complex.lt_def.1 (mapsTo_moebBall q u hu ht τ).det_pos).1
  have e' := det_transpose_eq (ballMat q (moebBall q u t) τ)
  rw [ballMat_moebBall, Matrix.transpose_transpose, ← ballMat_moebBall] at e'
  rw [← e', ← det_transpose_eq] at hD
  rw [hD, Complex.re_ofReal_mul, Real.log_mul (by positivity) hpos.ne', Real.log_pow]
  push_cast; ring

theorem moebBall_props : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) →
    DifferentiableOn ℂ (moebBall q u) (ballDom q) ∧ Set.MapsTo (moebBall q u) (ballDom q) (ballDom q) ∧
      ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ballDom q) ∧
        ∀ t ∈ ballDom q, ballPot q (moebBall q u t) = ballPot q t + (G t).re := by
  intro Ψ _ j j' n q u hu
  refine ⟨differentiableOn_moebBall q u hu, mapsTo_moebBall q u hu, ?_⟩
  have hne : ∀ t ∈ ballDom q, ∀ τ, (den (u τ) (ballMat q t τ)ᵀ).det ≠ 0 :=
    fun t ht τ => den_det_ne (hu τ) (ball_transpose ht τ)
  obtain ⟨L, hL, hLe⟩ := GroundTheory.Heights₂.Heights.Regular.exists_analytic_log
    (GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.isOpen_ballDom q) (convex_ballDom q) ⟨0, zero_mem q⟩
    (h := fun t => ∏ τ, (den (u τ) (ballMat q t τ)ᵀ).det)
    (fun t _ => Finset.analyticAt_fun_prod _ fun τ _ =>
      analyticAt_det_entries _ t (analyticAt_den_entry q (u τ) τ t))
    (fun t ht => Finset.prod_ne_zero_iff.2 fun τ _ => hne t ht τ)
  refine ⟨fun t => 2 * L t, (hL.differentiableOn).const_mul 2, fun t ht => ?_⟩
  have hre : (L t).re = ∑ τ, Real.log ‖(den (u τ) (ballMat q t τ)ᵀ).det‖ := by
    have h1 := congrArg norm (hLe t ht)
    rw [Complex.norm_exp, norm_prod] at h1
    rw [← Real.log_prod (fun τ _ => norm_ne_zero_iff.2 (hne t ht τ)), ← h1, Real.log_exp]
  have h2 : (2 * L t).re = 2 * (L t).re := by simp
  simp only [ballPot]
  rw [h2, hre, Finset.mul_sum, Finset.sum_congr rfl fun τ _ => log_det_moeb q u hu ht τ,
    Finset.sum_sub_distrib]
  ring
end Hol

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb
