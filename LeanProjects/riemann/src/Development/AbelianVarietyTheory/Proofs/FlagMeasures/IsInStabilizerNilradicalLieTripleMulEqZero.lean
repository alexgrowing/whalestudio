import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiiIff

open GlobalTheory.Count Formalism.MainNotions.S Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.NilLie

open GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.UG

section Algebra

variable {K : Type} [Field K] {n : ℕ} {s : K →+* K} {J : Matrix (Fin n) (Fin n) K}
  {W : Submodule K (Fin n → K)}

def ex (Y : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := 1 + Y + (2 : K)⁻¹ • (Y * Y)

theorem ext_mulVec {M N : Matrix (Fin n) (Fin n) K} (h : ∀ u, M *ᵥ u = N *ᵥ u) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun u => by simpa using h u)

theorem perp_add {u u' : Fin n → K} (h : u ∈ perpSet s J W) (h' : u' ∈ perpSet s J W) :
    u + u' ∈ perpSet s J W := fun w hw => by
  have h1 := h w hw
  have h2 := h' w hw
  rw [GlobalTheory.CoverRadiiEq.hform_eq_dot] at *
  rw [mulVec_add, dotProduct_add, h1, h2, add_zero]

theorem perp_smul (c : K) {u : Fin n → K} (h : u ∈ perpSet s J W) :
    c • u ∈ perpSet s J W := fun w hw => by
  have h1 := h w hw
  rw [GlobalTheory.CoverRadiiEq.hform_eq_dot] at *
  rw [mulVec_smul, dotProduct_smul, h1, smul_zero]

theorem cT_add (M N : Matrix (Fin n) (Fin n) K) : cT s (M + N) = cT s M + cT s N := by
  ext i j; simp [cT]

theorem cT_sub (M N : Matrix (Fin n) (Fin n) K) : cT s (M - N) = cT s M - cT s N := by
  ext i j; simp [cT]

theorem cT_smul (c : K) (M : Matrix (Fin n) (Fin n) K) : cT s (c • M) = s c • cT s M := by
  ext i j; simp [cT]

theorem cT_zero : cT s (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  ext i j; simp [cT]

theorem skew_eq {Y : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) : cT s Y * J = -(J * Y) :=
  eq_neg_of_add_eq_zero_left ((GlobalTheory.CoverRadiiEq.skew_iff s J Y).2 h.1)

theorem nil_add {Y Y' : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) (h' : InNil s J W Y') :
    InNil s J W (Y + Y') := by
  refine ⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [cT_add, add_mul, skew_eq h, skew_eq h', mul_add]; abel
  · rw [add_mulVec]; exact perp_add (h.2.1 u) (h'.2.1 u)
  · rw [add_mulVec]; exact W.add_mem (h.2.2.1 u hu) (h'.2.2.1 u hu)
  · rw [add_mulVec, h.2.2.2 u hu, h'.2.2.2 u hu, add_zero]

theorem nil_smul {c : K} (hc : s c = c) {Y : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) :
    InNil s J W (c • Y) := by
  refine ⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [cT_smul, hc, smul_mul_assoc, skew_eq h, mul_smul_comm, smul_neg, neg_add_cancel]
  · rw [smul_mulVec]; exact perp_smul c (h.2.1 u)
  · rw [smul_mulVec]; exact W.smul_mem c (h.2.2.1 u hu)
  · rw [smul_mulVec, h.2.2.2 u hu, smul_zero]

theorem nil_neg {Y : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) : InNil s J W (-Y) := by
  simpa using nil_smul (c := -1) (by simp) h

theorem nil_sub {Y Y' : Matrix (Fin n) (Fin n) K} (h : InNil s J W Y) (h' : InNil s J W Y') :
    InNil s J W (Y - Y') := by
  rw [sub_eq_add_neg]; exact nil_add h (nil_neg h')

theorem cen_add {Y Y' : Matrix (Fin n) (Fin n) K} (h : InCen s J W Y) (h' : InCen s J W Y') :
    InCen s J W (Y + Y') :=
  ⟨nil_add h.1 h'.1, fun u hu => by rw [add_mulVec, h.2 u hu, h'.2 u hu, add_zero]⟩

theorem cen_smul {c : K} (hc : s c = c) {Y : Matrix (Fin n) (Fin n) K} (h : InCen s J W Y) :
    InCen s J W (c • Y) :=
  ⟨nil_smul hc h.1, fun u hu => by rw [smul_mulVec, h.2 u hu, smul_zero]⟩

theorem cen_sub {Y Y' : Matrix (Fin n) (Fin n) K} (h : InCen s J W Y) (h' : InCen s J W Y') :
    InCen s J W (Y - Y') :=
  ⟨nil_sub h.1 h'.1, fun u hu => by rw [sub_mulVec, h.2 u hu, h'.2 u hu, sub_zero]⟩

theorem isInStabilizerNilradicalLie_triple_mul_eq_zero {a b c : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) (hb : InNil s J W b)
    (hc : InNil s J W c) : a * (b * c) = 0 :=
  ext_mulVec fun u => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
    exact ha.2.2.2 _ (hb.2.2.1 _ (hc.2.1 u))

theorem cen_mul_nil {Z Y : Matrix (Fin n) (Fin n) K} (hZ : InCen s J W Z) (hY : InNil s J W Y) :
    Z * Y = 0 :=
  ext_mulVec fun u => by
    rw [← mulVec_mulVec, zero_mulVec]
    exact hZ.2 _ (hY.2.1 u)

theorem nil_mul_cen (hJ : IsUnit J) {Z Y : Matrix (Fin n) (Fin n) K} (hY : InNil s J W Y)
    (hZ : InCen s J W Z) : Y * Z = 0 := by
  have h : cT s (Z * Y) * J = J * (Y * Z) := by
    rw [cT_mul, mul_assoc, skew_eq hZ.1, mul_neg, ← mul_assoc, skew_eq hY, neg_mul, neg_neg, mul_assoc]
  rw [cen_mul_nil hZ hY, cT_zero, zero_mul] at h
  exact hJ.mul_right_eq_zero.1 h.symm

theorem cen_comm {a b : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) (hb : InNil s J W b) :
    InCen s J W (a * b - b * a) := by
  have h0 : ∀ u ∈ perpSet s J W, (a * b - b * a) *ᵥ u = 0 := fun u hu => by
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ha.2.2.2 _ (hb.2.2.1 _ hu),
      hb.2.2.2 _ (ha.2.2.1 _ hu), sub_zero]
  refine ⟨⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩, h0⟩
  · rw [cT_sub, cT_mul, cT_mul, sub_mul, mul_assoc, mul_assoc, skew_eq ha, skew_eq hb, mul_neg, mul_neg,
      ← mul_assoc, ← mul_assoc, skew_eq ha, skew_eq hb]
    noncomm_ring
  · rw [sub_eq_add_neg, add_mulVec, ← neg_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact perp_add (ha.2.1 _) ((nil_neg hb).2.1 _)
  · rw [h0 u hu]; exact W.zero_mem
  · rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ha.2.2.2 u hu, hb.2.2.2 u hu, mulVec_zero,
      mulVec_zero, sub_zero]

variable [CharZero K]

theorem map_half : s (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]

theorem ex_mul_ex {a b : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) (hb : InNil s J W b) :
    ex a * ex b = 1 + a + b + (2 : K)⁻¹ • (a * a) + (2 : K)⁻¹ • (b * b) + a * b := by
  have h1 := isInStabilizerNilradicalLie_triple_mul_eq_zero ha ha hb
  have h2 := isInStabilizerNilradicalLie_triple_mul_eq_zero ha hb hb
  simp only [ex, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc, h1, h2,
    mul_zero, smul_zero, add_zero]
  abel

theorem ex_mul_ex_neg {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) : ex a * ex (-a) = 1 := by
  rw [ex_mul_ex ha (nil_neg ha)]
  simp only [neg_mul, mul_neg, neg_neg]
  module

theorem ex_neg_mul_ex {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) : ex (-a) * ex a = 1 := by
  simpa using ex_mul_ex_neg (nil_neg ha)

theorem ex_add_cen (hJ : IsUnit J) {Y Z : Matrix (Fin n) (Fin n) K} (hY : InNil s J W Y)
    (hZ : InCen s J W Z) : ex (Y + Z) = ex Y + Z := by
  simp only [ex, add_mul, mul_add, cen_mul_nil hZ hY, nil_mul_cen hJ hY hZ, cen_mul_nil hZ hZ.1, add_zero]
  abel

theorem ex_mul_ex_cen (hJ : IsUnit J) {Y Z : Matrix (Fin n) (Fin n) K} (hY : InNil s J W Y)
    (hZ : InCen s J W Z) : ex Y * ex Z = ex (Y + Z) := by
  rw [ex_add_cen hJ hY hZ, ex_mul_ex hY hZ.1, nil_mul_cen hJ hY hZ, cen_mul_nil hZ hZ.1, ex]
  simp only [smul_zero, add_zero]
  abel

theorem ex_factor (hJ : IsUnit J) {Y₀ A Z₁ Z' : Matrix (Fin n) (Fin n) K} (h₀ : InNil s J W Y₀)
    (hA : InNil s J W A) (h₁ : InCen s J W Z₁) (h' : InCen s J W Z') :
    ex (Y₀ + A + (Z₁ + Z' - (2 : K)⁻¹ • (A * Y₀ - Y₀ * A))) = ex (Y₀ + Z₁) * ex A * ex Z' := by
  rw [ex_add_cen hJ (nil_add h₀ hA) (cen_sub (cen_add h₁ h') (cen_smul map_half (cen_comm hA h₀))),
    mul_assoc, ex_mul_ex_cen hJ hA h', ex_mul_ex (nil_add h₀ h₁.1) (nil_add hA h'.1), ex]
  simp only [add_mul, mul_add, cen_mul_nil h₁ h₀, cen_mul_nil h₁ hA, cen_mul_nil h₁ h₁.1,
    cen_mul_nil h₁ h'.1, cen_mul_nil h' hA, cen_mul_nil h' h'.1, nil_mul_cen hJ h₀ h₁,
    nil_mul_cen hJ h₀ h', nil_mul_cen hJ hA h', add_zero]
  module

theorem ex_unitary {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) : cT s (ex a) * J * ex a = J := by
  have h : cT s (ex a) * J = J * ex (-a) := by
    rw [ex, cT_add, cT_add, cT_one, cT_smul, map_half, cT_mul, add_mul, add_mul, smul_mul_assoc, mul_assoc,
      skew_eq ha, mul_neg, ← mul_assoc, skew_eq ha, ex]
    simp only [mul_add, neg_mul, mul_neg, neg_neg, one_mul, mul_one, mul_smul_comm, mul_assoc]
  rw [h, mul_assoc, ex_neg_mul_ex ha, mul_one]

theorem ex_unip {a : Matrix (Fin n) (Fin n) K} (ha : InNil s J W a) :
    (∀ x ∈ W, (ex a - 1) *ᵥ x = 0) ∧ (∀ y ∈ perpSet s J W, (ex a - 1) *ᵥ y ∈ W) ∧
      ∀ y, (ex a - 1) *ᵥ y ∈ perpSet s J W := by
  have h : ∀ y, (ex a - 1) *ᵥ y = a *ᵥ y + (2 : K)⁻¹ • (a *ᵥ (a *ᵥ y)) := fun y => by
    rw [mulVec_mulVec, ← smul_mulVec, ← add_mulVec, ex]; congr 1; abel
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [h, ha.2.2.2 x hx]; simp
  · rw [h, ha.2.2.2 _ (ha.2.2.1 y hy)]; simpa using ha.2.2.1 y hy
  · rw [h]; exact perp_add (ha.2.1 _) (perp_smul _ (ha.2.1 _))

theorem exists_log {g : Matrix (Fin n) (Fin n) K} (hU : cT s g * J * g = J)
    (h : (∀ x ∈ W, (g - 1) *ᵥ x = 0) ∧ (∀ y ∈ perpSet s J W, (g - 1) *ᵥ y ∈ W) ∧
      ∀ y, (g - 1) *ᵥ y ∈ perpSet s J W) : ∃ Y, InNil s J W Y ∧ ex Y = g := by
  obtain ⟨N, rfl⟩ : ∃ N, g = 1 + N := ⟨g - 1, by abel⟩
  rw [add_sub_cancel_left] at h
  have h3 : N * (N * N) = 0 := ext_mulVec fun u => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
    exact h.1 _ (h.2.1 _ (h.2.2 u))
  have hv : ∀ y, (N - (2 : K)⁻¹ • (N * N)) *ᵥ y = N *ᵥ y + (-(2 : K)⁻¹) • (N *ᵥ (N *ᵥ y)) := fun y => by
    rw [mulVec_mulVec, ← smul_mulVec, ← add_mulVec, neg_smul, sub_eq_add_neg]
  have hinv : (1 + N) * (1 - N + N * N) = 1 := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, h3]; abel
  have hN : cT s N * J = J * (N * N - N) := by
    have h1 : cT s (1 + N) * J = J * (1 - N + N * N) := by
      conv_rhs => rw [← hU]
      rw [mul_assoc, hinv, mul_one]
    rw [cT_add, cT_one, add_mul, one_mul] at h1
    rw [eq_sub_of_add_eq' h1]; noncomm_ring
  refine ⟨N - (2 : K)⁻¹ • (N * N),
    ⟨(GlobalTheory.CoverRadiiEq.skew_iff s J _).1 ?_, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩, ?_⟩
  · rw [cT_sub, cT_smul, map_half, cT_mul, sub_mul, smul_mul_assoc, mul_assoc, hN, ← mul_assoc, hN]
    simp only [mul_sub, sub_mul, mul_assoc, h3, mul_zero, mul_smul_comm]
    module
  · rw [hv]; exact perp_add (h.2.2 _) (perp_smul _ (h.2.2 _))
  · rw [hv, h.1 _ (h.2.1 u hu)]; simpa using h.2.1 u hu
  · rw [hv, h.1 u hu]; simp
  · simp only [ex, mul_sub, sub_mul, mul_assoc, h3, mul_zero, mul_smul_comm, smul_mul_assoc]
    module

end Algebra

section Complex

variable {n : ℕ}

theorem exp_eq_ex {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y * (Y * Y) = 0) : NormedSpace.exp Y = ex Y := by
  have h3 : Y ^ 3 = 0 := by rw [pow_succ', pow_two, h]
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  dsimp only
  rw [tsum_eq_sum (s := range 3)]
  · simp [Finset.sum_range_succ, ex, pow_two, Nat.factorial]
  · intro k hk
    have : 3 ≤ k := by simpa using hk
    rw [pow_eq_zero_of_le this h3, smul_zero]

theorem ex_conj {G Gi : Matrix (Fin n) (Fin n) ℂ} (h : G * Gi = 1) (h' : Gi * G = 1)
    (Y : Matrix (Fin n) (Fin n) ℂ) : ex (Gi * Y * G) = Gi * ex Y * G := by
  have : Gi * Y * G * (Gi * Y * G) = Gi * (Y * Y) * G := by
    calc _ = Gi * Y * (G * Gi) * Y * G := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, one_mul]
  simp only [ex, this, mul_add, add_mul, mul_one, h', mul_smul_comm, smul_mul_assoc]

theorem exp_conj {G Gi : Matrix (Fin n) (Fin n) ℂ} (h : G * Gi = 1) (h' : Gi * G = 1)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y * (Y * Y) = 0) :
    NormedSpace.exp (Gi * Y * G) = Gi * ex Y * G := by
  rw [exp_eq_ex, ex_conj h h']
  calc _ = Gi * Y * (G * Gi) * Y * (G * Gi) * Y * G := by simp only [mul_assoc]
    _ = Gi * (Y * (Y * Y)) * G := by rw [h]; simp only [mul_assoc, one_mul]
    _ = 0 := by rw [hY, mul_zero, zero_mul]

theorem cT_conj (M : Matrix (Fin n) (Fin n) ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [cT]

theorem hs_smul (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : hs (c • M) = ‖c‖ ^ 2 * hs M := by
  simp [hs, Finset.mul_sum, mul_pow]

end Complex

section Point

variable (I : AutInst)

theorem normAt_smul (x : I.GA) (c : ℝ) (hc : 0 ≤ c) (D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :
    normAt I x (fun v => (c : ℂ) • D v) = c * normAt I x D := by
  unfold normAt
  simp only [mul_smul_comm, smul_mul_assoc, hs_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem P_mul_inv (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem inv_mul_P (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : uMat u * uMat u⁻¹ = 1 := by
  simp [uMat]

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : uMat u⁻¹ * uMat u = 1 := by
  simp [uMat]

theorem frame_mul (x : I.GA) (v : InfinitePlace I.F) :
    I.P v * uMat (x.1 v) * (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) = 1 := by
  rw [mul_assoc, ← mul_assoc (uMat (x.1 v)), uMat_mul_inv, one_mul, P_mul_inv]

theorem mul_frame (x : I.GA) (v : InfinitePlace I.F) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * (I.P v * uMat (x.1 v)) = 1 := by
  rw [mul_assoc, ← mul_assoc (I.P v)⁻¹, inv_mul_P, one_mul, uMat_inv_mul]

theorem isUnit_Jv (v : InfinitePlace I.F) : IsUnit (I.J.map (I.φ v)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have := (I.φ v).map_det I.J
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact (map_ne_zero _).2 I.J_det

theorem inG_frame (x : I.GA) (v : InfinitePlace I.F) {W : Submodule ℂ (Fin I.n → ℂ)}
    {A : Matrix (Fin I.n) (Fin I.n) ℂ} (hA : InNil (starRingEnd ℂ) (I.J.map (I.φ v)) W A) :
    inG (I.ε v) (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * A * (I.P v * uMat (x.1 v))) := by
  have hx : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  have h0 : (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
    rw [← hx, ← I.P_spec v, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h1 := frame_mul I x v
  have h2 := skew_eq hA
  rw [cT_conj] at h2
  unfold inG
  rw [← h0]
  generalize I.P v * uMat (x.1 v) = G at *
  generalize uMat (x.1 v)⁻¹ * (I.P v)⁻¹ = Gi at *
  calc _ = Gᴴ * Aᴴ * (G * Gi)ᴴ * I.J.map (I.φ v) * G + Gᴴ * I.J.map (I.φ v) * (G * Gi) * A * G := by
        simp only [conjTranspose_mul, mul_assoc]
    _ = Gᴴ * (Aᴴ * I.J.map (I.φ v)) * G + Gᴴ * (I.J.map (I.φ v) * A) * G := by
        rw [h1]; simp only [conjTranspose_one, mul_one, mul_assoc]
    _ = 0 := by rw [h2]; simp

end Point

end GlobalTheory.NilLie
