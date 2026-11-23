import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.HermitianFormFactor

section Defs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def cm {m Q : Type} (Y : Q → m → ℂ) : Matrix m Q ℂ := fun i j => Y j i

structure Frame {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (Em : Matrix m Q ℂ) : Prop where
  pp : Epᴴ * Ep = 1
  mm : Emᴴ * Em = 1
  pm : Epᴴ * Em = 0
  sum : Ep * Epᴴ + Em * Emᴴ = 1
  diff : Ep * Epᴴ - Em * Emᴴ = H

def Tm {m Q : Type} [Fintype m] (H : Matrix m m ℂ) (Y : Matrix m Q ℂ) : Matrix Q Q ℂ := -(Yᴴ * H * Y)

def qf {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q] (T : Matrix Q Q ℂ) (B : Matrix P Q ℂ) : ℝ :=
  (Matrix.trace (B * T⁻¹ * Bᴴ)).re

def bet {m P Q : Type} [Fintype m] [Fintype P] [Fintype Q] (Ep : Matrix m P ℂ) (Em : Matrix m Q ℂ) (g : Matrix m m ℂ) : ℝ :=
  (Matrix.trace ((Epᴴ * g * Em) * (Epᴴ * g * Em)ᴴ)).re

end Defs

section Alg
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}

theorem Tm_mul_left {g : Matrix m m ℂ} (hg : g ∈ UH H) (Y : Matrix m Q ℂ) : Tm H (g * Y) = Tm H Y := by
  have hg' : gᴴ * H * g = H := hg
  unfold Tm
  rw [Matrix.conjTranspose_mul, show Yᴴ * gᴴ * H * (g * Y) = Yᴴ * (gᴴ * H * g) * Y by
    simp only [Matrix.mul_assoc], hg']

theorem Tm_coord (F : Frame H Ep Em) (Y : Matrix m Q ℂ) :
    Tm H Y = (Emᴴ * Y)ᴴ * (Emᴴ * Y) - (Epᴴ * Y)ᴴ * (Epᴴ * Y) := by
  unfold Tm
  rw [← F.diff]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, neg_sub]

namespace Frame

theorem mp (F : Frame H Ep Em) : Emᴴ * Ep = 0 := by
  have h := congrArg Matrix.conjTranspose F.pm
  simpa using h

theorem herm (F : Frame H Ep Em) : Hᴴ = H := by
  rw [← F.diff]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem H_Ep (F : Frame H Ep Em) : H * Ep = Ep := by
  rw [← F.diff, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, F.pp, F.mp, Matrix.mul_one, Matrix.mul_zero,
    sub_zero]

theorem H_Em (F : Frame H Ep Em) : H * Em = -Em := by
  rw [← F.diff, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, F.pm, F.mm, Matrix.mul_zero, Matrix.mul_one,
    zero_sub]

theorem Ep_H (F : Frame H Ep Em) : Epᴴ * H = Epᴴ := by
  have h := congrArg Matrix.conjTranspose F.H_Ep
  rwa [Matrix.conjTranspose_mul, F.herm] at h

theorem Em_H (F : Frame H Ep Em) : Emᴴ * H = -Emᴴ := by
  have h := congrArg Matrix.conjTranspose F.H_Em
  rwa [Matrix.conjTranspose_mul, F.herm, Matrix.conjTranspose_neg] at h

end Frame

theorem Tm_Em_mul (F : Frame H Ep Em) (a : Matrix Q Q ℂ) : Tm H (Em * a) = aᴴ * a := by
  have h : (Em * a)ᴴ * H * (Em * a) = -(aᴴ * a) := by
    rw [Matrix.conjTranspose_mul, show aᴴ * Emᴴ * H * (Em * a) = aᴴ * ((Emᴴ * H) * Em) * a by
      simp only [Matrix.mul_assoc], F.Em_H, Matrix.neg_mul, F.mm, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one]
  unfold Tm
  rw [h, neg_neg]

theorem qf_orbit (F : Frame H Ep Em) {g : Matrix m m ℂ} {a : Matrix Q Q ℂ} (hg : g ∈ UH H) (ha : IsUnit a.det) :
    qf (Tm H (g * Em * a)) (Epᴴ * (g * Em * a)) = bet Ep Em g := by
  have hT : Tm H (g * Em * a) = aᴴ * a := by
    rw [Matrix.mul_assoc, Tm_mul_left hg, Tm_Em_mul F]
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  rw [hT]
  unfold qf bet
  rw [Matrix.mul_inv_rev]
  congr 2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ ha', Matrix.mul_nonsing_inv_cancel_left _ _ ha]

open scoped MatrixOrder in
theorem posDef_factor {T : Matrix Q Q ℂ} (hT : T.PosDef) : ∃ a : Matrix Q Q ℂ, IsUnit a.det ∧ T = aᴴ * a := by
  obtain ⟨a, ha⟩ : ∃ a : Matrix Q Q ℂ, T = aᴴ * a := by
    first
    | exact ⟨CFC.sqrt T, by
        have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT.posSemidef
        have hs : (CFC.sqrt T)ᴴ = CFC.sqrt T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
        rw [hs, CFC.sqrt_mul_sqrt_self T h0]⟩
    | exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hT.posSemidef
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.mp hT.posSemidef
    | exact Matrix.PosSemidef.exists_eq_conjTranspose_mul_self hT.posSemidef
  refine ⟨a, ?_, ha⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := hT.det_pos
  rw [ha, Matrix.det_mul, h0, mul_zero] at hd
  exact lt_irrefl _ hd

theorem det_norm_one {g : Matrix m m ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : ‖g.det‖ = 1 := by
  have h := congrArg Matrix.det (show gᴴ * H * g = H from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have h1 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hH.ne_zero
    linear_combination h
  have h2 : (Complex.normSq g.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h1
  have h3 : Complex.normSq g.det = 1 := by exact_mod_cast h2
  have h4 : ‖g.det‖ ^ 2 = 1 := by
    first
    | rw [Complex.sq_norm]; exact h3
    | rw [← Complex.normSq_eq_norm_sq]; exact h3
  rw [← Real.sqrt_sq (norm_nonneg _), h4, Real.sqrt_one]

theorem frame_trans (F : Frame H Ep Em) (Y : Matrix m Q ℂ) (hY : (Tm H Y).PosDef) :
    ∃ g ∈ UH H, ∃ a : Matrix Q Q ℂ, IsUnit a.det ∧ Y = g * Em * a := by
  obtain ⟨a, ha, hTa⟩ := posDef_factor hY
  have ha' : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  set Y₀ : Matrix m Q ℂ := Y * a⁻¹ with hY₀
  have hYHY : Yᴴ * H * Y = -(aᴴ * a) := by
    rw [← hTa]; unfold Tm; simp
  have h1 : Y₀ᴴ * H * Y₀ = -1 := by
    rw [hY₀, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    have : aᴴ⁻¹ * Yᴴ * H * (Y * a⁻¹) = aᴴ⁻¹ * (Yᴴ * H * Y) * a⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, hYHY, Matrix.mul_neg, Matrix.neg_mul]
    have : aᴴ⁻¹ * (aᴴ * a) * a⁻¹ = (aᴴ⁻¹ * aᴴ) * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_nonsing_inv _ ha, Matrix.nonsing_inv_mul _ ha']; simp
  set b : Matrix P Q ℂ := Epᴴ * Y₀ with hb
  have hbH : bᴴ = Y₀ᴴ * Ep := by rw [hb, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hS : (1 + b * bᴴ).PosDef := Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose b)
  obtain ⟨β, hβ, hSβ⟩ := posDef_factor hS
  have hβ' : IsUnit βᴴ.det := by rw [Matrix.det_conjTranspose]; exact hβ.star
  set Z₁ : Matrix m P ℂ := Ep + Y₀ * bᴴ with hZ₁
  have h2 : Y₀ᴴ * H * Z₁ = 0 := by
    rw [hZ₁, Matrix.mul_add, Matrix.mul_assoc, F.H_Ep, ← Matrix.mul_assoc, h1, ← hbH]; simp
  have h3 : Z₁ᴴ * H * Z₁ = 1 + b * bᴴ := by
    have e1 : Z₁ᴴ = Epᴴ + b * Y₀ᴴ := by
      rw [hZ₁, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [e1, Matrix.add_mul, Matrix.add_mul, F.Ep_H]
    have e2 : b * Y₀ᴴ * H * Z₁ = b * (Y₀ᴴ * H * Z₁) := by simp only [Matrix.mul_assoc]
    rw [e2, h2, Matrix.mul_zero, add_zero, hZ₁, Matrix.mul_add, F.pp, ← Matrix.mul_assoc, ← hb]
  set Z : Matrix m P ℂ := Z₁ * β⁻¹ with hZ
  have h4 : Y₀ᴴ * H * Z = 0 := by
    rw [hZ, ← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have h5 : Zᴴ * H * Y₀ = 0 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul, F.herm, Matrix.mul_assoc] using this
  have h6 : Zᴴ * H * Z = 1 := by
    rw [hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    have : βᴴ⁻¹ * Z₁ᴴ * H * (Z₁ * β⁻¹) = βᴴ⁻¹ * (Z₁ᴴ * H * Z₁) * β⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, h3, hSβ]
    have : βᴴ⁻¹ * (βᴴ * β) * β⁻¹ = (βᴴ⁻¹ * βᴴ) * (β * β⁻¹) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_nonsing_inv _ hβ, Matrix.nonsing_inv_mul _ hβ']; simp
  refine ⟨Y₀ * Emᴴ + Z * Epᴴ, ?_, a, ha, ?_⟩
  · show (Y₀ * Emᴴ + Z * Epᴴ)ᴴ * H * (Y₀ * Emᴴ + Z * Epᴴ) = H
    have : (Y₀ * Emᴴ + Z * Epᴴ)ᴴ * H * (Y₀ * Emᴴ + Z * Epᴴ) =
        Em * (Y₀ᴴ * H * Y₀) * Emᴴ + Em * (Y₀ᴴ * H * Z) * Epᴴ + Ep * (Zᴴ * H * Y₀) * Emᴴ +
          Ep * (Zᴴ * H * Z) * Epᴴ := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [this, h1, h4, h5, h6, ← F.diff]
    simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    abel
  · rw [Matrix.add_mul, Matrix.mul_assoc Y₀, F.mm, Matrix.mul_assoc Z, F.pm, Matrix.mul_zero, add_zero, Matrix.mul_one,
      hY₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]

theorem gN_sq {k r : ℕ} (A : Mat k r) : gN A ^ 2 = (Matrix.trace (A * Aᴴ)).re := by
  rw [gN, Real.sq_sqrt]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem Ppos_eq {k r : ℕ} {Ep : Matrix (Fin (2 * r + k + 1)) P ℂ} {Em : Matrix (Fin (2 * r + k + 1)) Q ℂ}
    (F : Frame (Hpk k r) Ep Em) : Ppos k r = Ep * Epᴴ := by
  unfold Ppos
  rw [← F.sum, ← F.diff]
  have h : Ep * Epᴴ + Em * Emᴴ + (Ep * Epᴴ - Em * Emᴴ) = (2 : ℂ) • (Ep * Epᴴ) := by
    rw [two_smul]; abel
  rw [h, smul_smul]
  norm_num

theorem Pneg_eq {k r : ℕ} {Ep : Matrix (Fin (2 * r + k + 1)) P ℂ} {Em : Matrix (Fin (2 * r + k + 1)) Q ℂ}
    (F : Frame (Hpk k r) Ep Em) : Pneg k r = Em * Emᴴ := by
  unfold Pneg
  rw [← F.sum, ← F.diff]
  have h : Ep * Epᴴ + Em * Emᴴ - (Ep * Epᴴ - Em * Emᴴ) = (2 : ℂ) • (Em * Emᴴ) := by
    rw [two_smul]; abel
  rw [h, smul_smul]
  norm_num

theorem bet_eq {k r : ℕ} {Ep : Matrix (Fin (2 * r + k + 1)) P ℂ} {Em : Matrix (Fin (2 * r + k + 1)) Q ℂ}
    (F : Frame (Hpk k r) Ep Em) (g : Mat k r) : bet Ep Em g = gN (Ppos k r * g * Pneg k r) ^ 2 := by
  rw [gN_sq, Ppos_eq F, Pneg_eq F]
  unfold bet
  rw [show Ep * Epᴴ * g * (Em * Emᴴ) = Ep * (Epᴴ * g * Em) * Emᴴ by simp only [Matrix.mul_assoc]]
  generalize Epᴴ * g * Em = B
  have h : Ep * B * Emᴴ * (Ep * B * Emᴴ)ᴴ = Ep * (B * Bᴴ) * Epᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Emᴴ Em, F.mm, Matrix.one_mul]
  rw [h, Matrix.trace_mul_comm (Ep * (B * Bᴴ)) Epᴴ, ← Matrix.mul_assoc, F.pp, Matrix.one_mul]

theorem mul_H_conj {g : Matrix m m ℂ} (h2 : H * H = 1) (hg : g ∈ UH H) : g * H * gᴴ = H := by
  have h1 : (H * gᴴ * H) * g = 1 := by
    rw [show H * gᴴ * H * g = H * (gᴴ * H * g) by simp only [Matrix.mul_assoc], show gᴴ * H * g = H from hg, h2]
  have h3 : g * (H * gᴴ * H) = 1 := by
    first
    | exact Matrix.mul_eq_one_comm.mp h1
    | exact mul_eq_one_comm.mp h1
    | rw [← Matrix.inv_eq_left_inv h1]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)
  calc g * H * gᴴ = g * H * gᴴ * (H * H) := by rw [h2, Matrix.mul_one]
    _ = g * (H * gᴴ * H) * H := by simp only [Matrix.mul_assoc]
    _ = H := by rw [h3, Matrix.one_mul]

private theorem trace_mul_conjTranspose_of_signature_preserving {n : Type} [Fintype n] [DecidableEq n] (A D g : Matrix n n ℂ)
    (hAA : A * A = A) (hDD : D * D = D) (hAD : A * D = 0) (hDA : D * A = 0) (hsum : A + D = 1)
    (h1 : g * (A - D) * gᴴ = A - D) (h2 : gᴴ * (A - D) * g = A - D) :
    Matrix.trace (g * gᴴ) = Matrix.trace A + Matrix.trace D + 4 * Matrix.trace (A * (g * D * gᴴ)) := by
  have I1 : g * A * gᴴ - g * D * gᴴ = A - D := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact h1
  have I2 : gᴴ * A * g - gᴴ * D * g = A - D := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact h2
  have e0 : Matrix.trace (g * gᴴ) = Matrix.trace (g * A * gᴴ) + Matrix.trace (g * D * gᴴ) := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.mul_add, hsum, Matrix.mul_one]
  have e1 : Matrix.trace (g * A * gᴴ) - Matrix.trace (g * D * gᴴ) = Matrix.trace A - Matrix.trace D := by
    rw [← Matrix.trace_sub, ← Matrix.trace_sub, I1]
  have e2 : Matrix.trace (g * D * gᴴ) =
      Matrix.trace (A * (g * D * gᴴ)) + Matrix.trace (D * (g * D * gᴴ)) := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, hsum, Matrix.one_mul]
  have e3 : Matrix.trace (D * (g * A * gᴴ)) - Matrix.trace (D * (g * D * gᴴ)) = - Matrix.trace D := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, I1, Matrix.mul_sub, hDA, hDD, zero_sub, Matrix.trace_neg]
  have e4 : Matrix.trace (A * (g * A * gᴴ)) - Matrix.trace (A * (g * D * gᴴ)) = Matrix.trace A := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, I1, Matrix.mul_sub, hAA, hAD, sub_zero]
  have e5 : Matrix.trace (A * (gᴴ * A * g)) - Matrix.trace (A * (gᴴ * D * g)) = Matrix.trace A := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, I2, Matrix.mul_sub, hAA, hAD, sub_zero]
  have e6 : Matrix.trace (A * (gᴴ * A * g)) = Matrix.trace (A * (g * A * gᴴ)) := by
    rw [Matrix.trace_mul_comm A (gᴴ * A * g), show gᴴ * A * g * A = gᴴ * (A * g * A) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm gᴴ, show A * g * A * gᴴ = A * (g * A * gᴴ) by
      simp only [Matrix.mul_assoc]]
  have e7 : Matrix.trace (A * (gᴴ * D * g)) = Matrix.trace (D * (g * A * gᴴ)) := by
    rw [Matrix.trace_mul_comm A (gᴴ * D * g), show gᴴ * D * g * A = gᴴ * (D * g * A) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm gᴴ, show D * g * A * gᴴ = D * (g * A * gᴴ) by
      simp only [Matrix.mul_assoc]]
  linear_combination e0 + e1 + 2 * e2 - 2 * e3 + 2 * e4 - 2 * e5 + 2 * e6 - 2 * e7

theorem hsblock : Formalism.FourierDecayAlt.B2.HSBlock := by
  intro k r g hg
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hH2 : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hAA : Ppos k r * Ppos k r = Ppos k r := by
    unfold Ppos
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hDD : Pneg k r * Pneg k r = Pneg k r := by
    unfold Pneg
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hAD : Ppos k r * Pneg k r = 0 := by
    unfold Ppos Pneg
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hDA : Pneg k r * Ppos k r = 0 := by
    unfold Ppos Pneg
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hsum : Ppos k r + Pneg k r = 1 := by
    unfold Ppos Pneg
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hdiff : Ppos k r - Pneg k r = Hpk k r := by
    unfold Ppos Pneg
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hAh : (Ppos k r)ᴴ = Ppos k r := by
    unfold Ppos
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hH]
    congr 1
    simp
  have hDh : (Pneg k r)ᴴ = Pneg k r := by
    unfold Pneg
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
    congr 1
    simp
  have h1 : g * (Ppos k r - Pneg k r) * gᴴ = Ppos k r - Pneg k r := by
    rw [hdiff]; exact mul_H_conj hH2 hg
  have h2 : gᴴ * (Ppos k r - Pneg k r) * g = Ppos k r - Pneg k r := by
    rw [hdiff]; exact hg
  have key := trace_mul_conjTranspose_of_signature_preserving (Ppos k r) (Pneg k r) g hAA hDD hAD hDA hsum h1 h2
  have htr : Matrix.trace (Ppos k r) + Matrix.trace (Pneg k r) = ((2 * r + k + 1 : ℕ) : ℂ) := by
    rw [← Matrix.trace_add, hsum, Matrix.trace_one, Fintype.card_fin]
  set A := Ppos k r with hA
  set D := Pneg k r with hD
  have hb : Matrix.trace (A * g * D * (A * g * D)ᴴ) = Matrix.trace (A * (g * D * gᴴ)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAh, hDh]
    rw [show A * g * D * (D * (gᴴ * A)) = A * (g * (D * D) * gᴴ * A) by simp only [Matrix.mul_assoc], hDD]
    rw [Matrix.trace_mul_comm, show g * D * gᴴ * A * A = g * D * gᴴ * (A * A) by simp only [Matrix.mul_assoc],
      hAA, Matrix.trace_mul_comm]
  have key2 : Matrix.trace (g * gᴴ) =
      ((2 * r + k + 1 : ℕ) : ℂ) + 4 * Matrix.trace (A * g * D * (A * g * D)ᴴ) := by
    rw [key, hb, htr]
  rw [gN_sq, gN_sq]
  have h3 := congrArg Complex.re key2
  simpa using h3

namespace Frame

theorem card_add (F : Frame H Ep Em) : (Fintype.card P : ℂ) + Fintype.card Q = Fintype.card m := by
  have h := congrArg Matrix.trace F.sum
  rw [Matrix.trace_add, Matrix.trace_mul_comm Ep, Matrix.trace_mul_comm Em, F.pp, F.mm] at h
  simpa using h

theorem card_sub (F : Frame H Ep Em) : (Fintype.card P : ℂ) - Fintype.card Q = H.trace := by
  have h := congrArg Matrix.trace F.diff
  rw [Matrix.trace_sub, Matrix.trace_mul_comm Ep, Matrix.trace_mul_comm Em, F.pp, F.mm] at h
  simpa using h

theorem reindex {P' Q' : Type} [Fintype P'] [DecidableEq P'] [Fintype Q'] [DecidableEq Q']
    (F : Frame H Ep Em) (eP : P' ≃ P) (eQ : Q' ≃ Q) :
    Frame H (Ep.submatrix id eP) (Em.submatrix id eQ) where
  pp := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, F.pp]
    exact Matrix.submatrix_one_equiv eP
  mm := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, F.mm]
    exact Matrix.submatrix_one_equiv eQ
  pm := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, F.pm]
    rfl
  sum := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    exact F.sum
  diff := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    exact F.diff

end Frame

theorem frame_fin (hH : H.IsHermitian) (h2 : H * H = 1) (a b : ℕ) (hab : Fintype.card m = a + b)
    (htr : H.trace = (a : ℂ) - b) :
    ∃ (Ep : Matrix m (Fin a) ℂ) (Em : Matrix m (Fin b) ℂ), Frame H Ep Em := by
  classical
  set U : Matrix m m ℂ := (hH.eigenvectorUnitary : Matrix m m ℂ) with hU
  set lam : m → ℝ := hH.eigenvalues with hlam
  have hU1 : Uᴴ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU2 : U * Uᴴ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have hspec : H = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set D : Matrix m m ℂ := Matrix.diagonal (fun i => (lam i : ℂ)) with hD
  have hDD : D * D = 1 := by
    have e1 : D = Uᴴ * H * U := by
      rw [hspec]
      have : Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      rw [this, hU1]; simp
    have e2 : D * D = Uᴴ * (H * (U * Uᴴ) * H) * U := by
      conv_lhs => rw [e1]
      simp only [Matrix.mul_assoc]
    rw [e2, hU2, Matrix.mul_one, h2, Matrix.mul_one, hU1]
  have hl : ∀ i, lam i = 1 ∨ lam i = -1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    have h3 : lam i * lam i = 1 := by exact_mod_cast this
    exact mul_self_eq_one_iff.mp h3
  let p : m → Prop := fun i => lam i = 1
  let Ep₀ : Matrix m {i // p i} ℂ := U.submatrix id Subtype.val
  let Em₀ : Matrix m {i // ¬ p i} ℂ := U.submatrix id Subtype.val
  have F₀ : Frame H Ep₀ Em₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have : Ep₀ᴴ * Ep₀ = (Uᴴ * U).submatrix Subtype.val Subtype.val := rfl
      rw [this, hU1]
      exact Matrix.submatrix_one _ Subtype.val_injective
    · have : Em₀ᴴ * Em₀ = (Uᴴ * U).submatrix Subtype.val Subtype.val := rfl
      rw [this, hU1]
      exact Matrix.submatrix_one _ Subtype.val_injective
    · have : Ep₀ᴴ * Em₀ = (Uᴴ * U).submatrix Subtype.val Subtype.val := rfl
      rw [this, hU1]
      ext i j
      have hne : i.val ≠ j.val := fun h => j.2 (h ▸ i.2)
      simp [hne]
    · ext i j
      have e := Fintype.sum_subtype_add_sum_subtype p (fun l => U i l * star (U j l))
      have e3 : (U * Uᴴ) i j = ∑ l, U i l * star (U j l) := by
        simp [Matrix.mul_apply]
      rw [← hU2, e3, ← e]
      simp [Matrix.mul_apply, Ep₀, Em₀]
    · ext i j
      have e := Fintype.sum_subtype_add_sum_subtype p (fun l => U i l * (lam l : ℂ) * star (U j l))
      have e3 : H i j = ∑ l, U i l * (lam l : ℂ) * star (U j l) := by
        conv_lhs => rw [hspec]
        simp [Matrix.mul_apply, hD, Matrix.diagonal_apply]
      rw [e3, ← e]
      have s1 : ∑ l : {l // p l}, U i l * (lam l : ℂ) * star (U j l) = ∑ l : {l // p l}, U i l * star (U j l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have : lam l = 1 := l.2
        rw [this]; simp
      have s2 : ∑ l : {l // ¬ p l}, U i l * (lam l : ℂ) * star (U j l) = - ∑ l : {l // ¬ p l}, U i l * star (U j l) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : lam l = -1 := (hl l).resolve_left l.2
        rw [this]; simp
      rw [s1, s2]
      simp [Matrix.mul_apply, Ep₀, Em₀, sub_eq_add_neg]
  have c1 := F₀.card_add
  have c2 := F₀.card_sub
  rw [hab] at c1
  rw [htr] at c2
  have hcP : Fintype.card {i // p i} = a := by
    have : ((Fintype.card {i // p i} : ℕ) : ℂ) = (a : ℂ) := by
      push_cast at c1
      linear_combination (1 / 2 : ℂ) * c1 + (1 / 2 : ℂ) * c2
    exact_mod_cast this
  have hcQ : Fintype.card {i // ¬ p i} = b := by
    have : ((Fintype.card {i // ¬ p i} : ℕ) : ℂ) = (b : ℂ) := by
      push_cast at c1
      linear_combination (1 / 2 : ℂ) * c1 - (1 / 2 : ℂ) * c2
    exact_mod_cast this
  exact ⟨_, _, F₀.reindex (Fintype.equivFinOfCardEq hcP).symm (Fintype.equivFinOfCardEq hcQ).symm⟩

theorem trace_Hpk (k r : ℕ) : (Hpk k r).trace = ((k + r : ℕ) : ℂ) - ((r + 1 : ℕ) : ℂ) := by
  have h1 : ∀ i : Fin (2 * r + k + 1), Hpk k r i i =
      (fun n : ℕ => (if r ≤ n ∧ n < r + k then (1 : ℂ) else 0) - (if n = r + k then 1 else 0)) i.val := by
    intro i
    unfold Hpk
    simp only [and_true]
    split_ifs <;> first | (exfalso; omega) | simp
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range
    (fun n : ℕ => (if r ≤ n ∧ n < r + k then (1 : ℂ) else 0) - (if n = r + k then 1 else 0)) (2 * r + k + 1),
    Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have f1 : (Finset.range (2 * r + k + 1)).filter (fun n => r ≤ n ∧ n < r + k) = Finset.Ico r (r + k) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have f2 : (Finset.range (2 * r + k + 1)).filter (fun n => n = r + k) = {r + k} := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
  rw [f1, f2]
  simp
  ring

theorem frame_exists (k r : ℕ) :
    ∃ (Ep : Matrix (Fin (2 * r + k + 1)) (Fin (k + r)) ℂ) (Em : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ),
      Frame (Hpk k r) Ep Em :=
  frame_fin (hpkFacts k r).1 (hpkFacts k r).2.1 (k + r) (r + 1) (by rw [Fintype.card_fin]; omega) (trace_Hpk k r)

end Alg

section Shear

lemma lintegral_normSq (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ z : ℂ, ψ (Complex.normSq z) = ENNReal.ofReal Real.pi * ∫⁻ s in Set.Ioi (0 : ℝ), ψ s := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h1 : ∀ p : ℝ × ℝ, Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 := by
    intro p
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [h1]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp only [smul_eq_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioo]
  have him : (fun x : ℝ => x ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact pow_pos (show (0 : ℝ) < x from hx) 2
    · intro hs
      exact ⟨Real.sqrt s, Real.sqrt_pos.2 hs, Real.sq_sqrt (le_of_lt hs)⟩
  have h2 := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioi (0 : ℝ)) (f := fun x : ℝ => x ^ 2)
    (f' := fun x => 2 * x) measurableSet_Ioi
    (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x hx y hy hxy => by
      have hx' : (0 : ℝ) ≤ x := le_of_lt hx
      have hy' : (0 : ℝ) ≤ y := le_of_lt hy
      exact (pow_left_inj₀ hx' hy' two_ne_zero).1 hxy) ψ
  rw [him] at h2
  rw [h2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have e1 : ENNReal.ofReal (Real.pi - -Real.pi) = ENNReal.ofReal Real.pi * 2 := by
    rw [show Real.pi - -Real.pi = Real.pi * 2 by ring, ENNReal.ofReal_mul Real.pi_pos.le]; simp
  have e2 : ENNReal.ofReal |2 * x| = 2 * ENNReal.ofReal x := by
    rw [abs_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num)]; simp
  simp only [e1, e2]
  ring

lemma polar_shift (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (h0 : ∀ s ≤ 0, φ s = 0) :
    ∫⁻ z : ℂ, φ (Complex.normSq z - 1) = ∫⁻ z : ℂ, φ (Complex.normSq z) := by
  rw [lintegral_normSq (fun s => φ (s - 1)) (hφ.comp (measurable_id.sub_const 1)), lintegral_normSq φ hφ]
  congr 1
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  rw [← lintegral_add_right_eq_self _ (1 : ℝ)]
  refine lintegral_congr fun s => ?_
  by_cases hs : 0 < s
  · have h1 : s + 1 ∈ Set.Ioi (0 : ℝ) := by show (0 : ℝ) < s + 1; linarith
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs)]
    simp
  · rw [Set.indicator_of_notMem (show s ∉ Set.Ioi (0 : ℝ) from hs)]
    by_cases h1 : s + 1 ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h1]
      simpa using h0 s (not_lt.1 hs)
    · rw [Set.indicator_of_notMem h1]

lemma lintegral_pi_congr_coord {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] [Inhabited E] (i : ι) (f f' : (ι → E) → ℝ≥0∞)
    (hf : Measurable f) (hf' : Measurable f')
    (h : ∀ x, ∫⁻ z, f (Function.update x i z) = ∫⁻ z, f' (Function.update x i z)) :
    ∫⁻ x, f x = ∫⁻ x, f' x := by
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => default), lintegral_eq_lmarginal_univ (fun _ => default),
    lmarginal_erase' _ hf (Finset.mem_univ i), lmarginal_erase' _ hf' (Finset.mem_univ i)]
  congr 2
  funext x
  exact h x

lemma lin_subst {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L L' : E →ₗ[ℝ] E) (h : L ∘ₗ L' = LinearMap.id) :
    ∃ c : ℝ≥0∞, ∀ f : E → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = c * ∫⁻ x, f (L x) ∂μ := by
  have hdet : LinearMap.det L ≠ 0 := by
    have h1 := congrArg LinearMap.det h
    rw [LinearMap.det_comp, LinearMap.det_id] at h1
    exact left_ne_zero_of_mul_eq_one h1
  refine ⟨ENNReal.ofReal |LinearMap.det L|, fun f hf => ?_⟩
  rw [← lintegral_map hf (LinearMap.continuous_of_finiteDimensional L).measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hdet, abs_one, ENNReal.ofReal_one, one_mul]

section gramsec

variable {Q : Type} [Fintype Q] [DecidableEq Q]

def gram (X : Q → Q → ℂ) : Matrix Q Q ℂ := (cm X)ᴴ * cm X

lemma gram_apply (X : Q → Q → ℂ) (i j : Q) : gram X i j = star (X i) ⬝ᵥ X j := rfl

lemma dot_conj (a b : Q → ℂ) : star a ⬝ᵥ b = star (star b ⬝ᵥ a) := by
  simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma gram_cont : Continuous (fun X : Q → Q → ℂ => (gram X : Q → Q → ℂ)) := by
  have hc : Continuous (fun X : Q → Q → ℂ => cm X) :=
    continuous_matrix fun i j => (continuous_apply i).comp (continuous_apply j)
  exact hc.matrix_conjTranspose.matrix_mul hc

lemma gram_update (X : Q → Q → ℂ) (j₀ : Q) (n x₀ : Q → ℂ) (hn1 : star n ⬝ᵥ n = 1)
    (hnX : ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0) (hx₀ : star n ⬝ᵥ x₀ = 0) (ζ : ℂ) :
    gram (Function.update X j₀ (x₀ + ζ • n)) =
      gram (Function.update X j₀ x₀) + (Complex.normSq ζ : ℂ) • Matrix.single j₀ j₀ (1 : ℂ) := by
  have hx₀' : star x₀ ⬝ᵥ n = 0 := by rw [dot_conj, hx₀, star_zero]
  have hnX' : ∀ j, j ≠ j₀ → star (X j) ⬝ᵥ n = 0 := fun j hj => by rw [dot_conj, hnX j hj, star_zero]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, gram_apply, gram_apply]
  by_cases hi : i = j₀
  · by_cases hj : j = j₀
    · subst hi; subst hj
      simp only [Function.update_self, star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, hn1, hx₀, hx₀', Matrix.single_apply_same, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
      rw [Complex.normSq_eq_conj_mul_self, mul_comm ζ]; rfl
    · subst hi
      simp only [Function.update_self, Function.update_of_ne hj, star_add, star_smul, add_dotProduct, smul_dotProduct,
        hnX j hj, smul_eq_mul, mul_zero, add_zero]
      rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj)]; simp
  · by_cases hj : j = j₀
    · subst hj
      simp only [Function.update_self, Function.update_of_ne hi, dotProduct_add, dotProduct_smul,
        hnX' i hi, smul_eq_mul, mul_zero, add_zero]
      rw [Matrix.single_apply_of_row_ne (Ne.symm hi)]; simp
    · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
      rw [Matrix.single_apply_of_row_ne (Ne.symm hi)]; simp

lemma not_posDef_of_sing (M : Matrix Q Q ℂ) (n : Q → ℂ) (hn : n ≠ 0) (hM : Mᴴ *ᵥ n = 0) (j₀ : Q) (s : ℝ) (hs : s ≤ 0) :
    ¬ (Mᴴ * M + (s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ)).PosDef := by
  intro hP
  have hd : Mᴴ.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨n, hn, hM⟩
  have hd' : M.det = 0 := by
    rw [Matrix.det_conjTranspose] at hd; exact star_eq_zero.mp hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd'
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hP hv
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero, zero_add] at hpos
  have hval : star v ⬝ᵥ (((s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ)) *ᵥ v) =
      ((s * Complex.normSq (v j₀) : ℝ) : ℂ) := by
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Complex.normSq_eq_conj_mul_self]
    rw [Finset.sum_eq_single j₀]
    · first
      | (simp; done)
      | (simp; ring)
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hval, Complex.zero_lt_real] at hpos
  nlinarith [Complex.normSq_nonneg (v j₀)]

end gramsec

section rankone

variable {Q : Type} [Fintype Q] [DecidableEq Q]

lemma lintegral_insertFiber_le (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (X : Q → Q → ℂ) (j₀ : Q) (n : Q → ℂ) (hn1 : star n ⬝ᵥ n = 1)
    (hnX : ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0) (w : Q → ℂ) :
    ∫⁻ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n)) - Matrix.single j₀ j₀ (1 : ℂ)) =
      ∫⁻ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n))) := by
  set α : ℂ := star n ⬝ᵥ w with hα
  set x₀ : Q → ℂ := w - α • n with hx₀def
  have hx₀ : star n ⬝ᵥ x₀ = 0 := by
    rw [hx₀def, dotProduct_sub, dotProduct_smul, hn1, ← hα]; simp
  have hw : ∀ z : ℂ, w + z • n = x₀ + (z + α) • n := by
    intro z; rw [hx₀def, add_smul]; abel
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn1; simp at hn1
  set M₀ : Matrix Q Q ℂ := gram (Function.update X j₀ x₀) with hM₀
  let φ : ℝ → ℝ≥0∞ := fun s => G₀ (M₀ + (s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ))
  have hφm : Measurable φ := by
    refine hG.comp (Continuous.measurable ?_)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hφ0 : ∀ s ≤ 0, φ s = 0 := by
    intro s hs
    refine h0 _ ?_
    refine not_posDef_of_sing (cm (Function.update X j₀ x₀)) n hn0 ?_ j₀ s hs
    funext j
    show star (Function.update X j₀ x₀ j) ⬝ᵥ n = 0
    rw [dot_conj]
    by_cases hj : j = j₀
    · subst hj; rw [Function.update_self, hx₀, star_zero]
    · rw [Function.update_of_ne hj, hnX j hj, star_zero]
  have e1 : ∀ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n)) - Matrix.single j₀ j₀ (1 : ℂ)) =
      φ (Complex.normSq (z + α) - 1) := by
    intro z
    rw [hw z, gram_update X j₀ n x₀ hn1 hnX hx₀]
    show _ = G₀ (M₀ + ((Complex.normSq (z + α) - 1 : ℝ) : ℂ) • Matrix.single j₀ j₀ (1 : ℂ))
    congr 1
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  have e2 : ∀ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n))) = φ (Complex.normSq (z + α)) := by
    intro z
    rw [hw z, gram_update X j₀ n x₀ hn1 hnX hx₀]
  simp_rw [e1, e2]
  rw [lintegral_add_right_eq_self (fun z : ℂ => φ (Complex.normSq z - 1)) α,
    lintegral_add_right_eq_self (fun z : ℂ => φ (Complex.normSq z)) α]
  exact polar_shift φ hφm hφ0

lemma exists_unit_orth (X : Q → Q → ℂ) (j₀ : Q) :
    ∃ n : Q → ℂ, star n ⬝ᵥ n = 1 ∧ ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0 := by
  have hd : ((cm (Function.update X j₀ 0))ᴴ).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero j₀ fun l => ?_
    simp [cm, Matrix.conjTranspose_apply]
  obtain ⟨n₀, hn₀, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  set ν : ℝ := ∑ l, Complex.normSq (n₀ l) with hν
  have hνc : star n₀ ⬝ᵥ n₀ = (ν : ℂ) := by
    simp only [dotProduct, Pi.star_apply, hν, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hνpos : 0 < ν := by
    have hne : ν ≠ 0 := by
      intro h
      apply hn₀
      have : star n₀ ⬝ᵥ n₀ = 0 := by rw [hνc, h]; simp
      exact dotProduct_star_self_eq_zero.1 this
    exact lt_of_le_of_ne (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Ne.symm hne)
  refine ⟨(((Real.sqrt ν)⁻¹ : ℝ) : ℂ) • n₀, ?_, fun j hj => ?_⟩
  · rw [star_smul, smul_dotProduct, dotProduct_smul, hνc]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    have := Real.sq_sqrt hνpos.le
    have h2 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.2 hνpos).ne'
    field_simp
    linarith
  · have h1 : star (X j) ⬝ᵥ n₀ = 0 := by
      have := congrFun hM j
      have e : ((cm (Function.update X j₀ 0))ᴴ *ᵥ n₀) j = star (Function.update X j₀ 0 j) ⬝ᵥ n₀ := rfl
      rw [e, Function.update_of_ne hj] at this
      exact this
    rw [star_smul, smul_dotProduct, dot_conj, h1]; simp

end rankone

section rankone2

variable {Q : Type} [Fintype Q] [DecidableEq Q]

lemma meas_gram_sub (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (C : Matrix Q Q ℂ) :
    Measurable fun X : Q → Q → ℂ => G₀ (gram X - C) := by
  have h : Measurable (fun X : Q → Q → ℂ => fun i j => gram X i j - C i j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (gram_cont.matrix_elem i j).measurable.sub_const (C i j)
  exact hG.comp h

lemma meas_gram (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) :
    Measurable fun X : Q → Q → ℂ => G₀ (gram X) := by
  have h : Measurable (fun X : Q → Q → ℂ => fun i j => gram X i j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => (gram_cont.matrix_elem i j).measurable
  exact hG.comp h

def colL (n : Q → ℂ) (c : ℂ) (i₀ : Q) : (Q → ℂ) →ₗ[ℝ] (Q → ℂ) where
  toFun x := x + (c * x i₀) • (n - Pi.single i₀ 1)
  map_add' x y := by
    funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  map_smul' a x := by
    funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul]; ring

lemma rank_one_std (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (j₀ : Q) :
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - Matrix.single j₀ j₀ (1 : ℂ)) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by
  refine lintegral_pi_congr_coord j₀ _ _ (meas_gram_sub G₀ hG _) (meas_gram G₀ hG) fun X => ?_
  obtain ⟨n, hn1, hnX⟩ := exists_unit_orth X j₀
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn1; simp at hn1
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hn0
  have hi₀' : n i₀ ≠ 0 := hi₀
  have hLL : colL n 1 i₀ ∘ₗ colL n (-(n i₀)⁻¹) i₀ = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    funext l
    simp only [LinearMap.comp_apply, colL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Pi.single_eq_same, LinearMap.id_apply]
    field_simp
    ring
  obtain ⟨c, hc⟩ := lin_subst (volume : Measure (Q → ℂ)) _ _ hLL
  have hup : Continuous fun x : Q → ℂ => Function.update X j₀ x := continuous_const.update j₀ continuous_id
  refine (hc (fun x => G₀ (gram (Function.update X j₀ x) - Matrix.single j₀ j₀ (1 : ℂ)))
    ((meas_gram_sub G₀ hG _).comp hup.measurable)).trans (Eq.trans ?_ (hc (fun x => G₀ (gram (Function.update X j₀ x)))
    ((meas_gram G₀ hG).comp hup.measurable)).symm)
  congr 1
  have hLc : Continuous (colL n 1 i₀) := (colL n 1 i₀).continuous_of_finiteDimensional
  refine lintegral_pi_congr_coord i₀ _ _ (((meas_gram_sub G₀ hG _).comp hup.measurable).comp hLc.measurable)
    (((meas_gram G₀ hG).comp hup.measurable).comp hLc.measurable) fun x' => ?_
  have hL : ∀ z : ℂ, colL n 1 i₀ (Function.update x' i₀ z) = Function.update x' i₀ 0 + z • n := by
    intro z
    funext l
    simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Function.update_self, one_mul]
    by_cases hl : l = i₀
    · subst hl; simp; ring
    · simp [hl]
  simp_rw [hL]
  exact lintegral_insertFiber_le G₀ hG h0 X j₀ n hn1 hnX _

def rmulL (A : Matrix Q Q ℂ) : (Q → Q → ℂ) →ₗ[ℝ] (Q → Q → ℂ) where
  toFun X := fun j i => (cm X * A) i j
  map_add' X Y := by
    funext j i; simp [cm, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a X := by
    funext j i; simp [cm, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

lemma cm_rmulL (A : Matrix Q Q ℂ) (X : Q → Q → ℂ) : cm (rmulL A X) = cm X * A := rfl

lemma gram_rmulL (A : Matrix Q Q ℂ) (X : Q → Q → ℂ) : gram (rmulL A X) = Aᴴ * gram X * A := by
  unfold gram
  rw [cm_rmulL, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma rmulL_comp (A A' : Matrix Q Q ℂ) (h : A' * A = 1) : rmulL A ∘ₗ rmulL A' = LinearMap.id := by
  apply LinearMap.ext
  intro X
  have h1 : cm (rmulL A (rmulL A' X)) = cm X := by
    rw [cm_rmulL, cm_rmulL, Matrix.mul_assoc, h, Matrix.mul_one]
  funext j i
  exact congrFun (congrFun h1 i) j

lemma rank_one (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (b : Q → ℂ) :
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - Matrix.vecMulVec (star b) b) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by
  by_cases hb : b = 0
  · subst hb; simp
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hb
  have hj₀' : b j₀ ≠ 0 := hj₀
  set A : Matrix Q Q ℂ := ((1 : Matrix Q Q ℂ).updateCol j₀ b)ᵀ with hA
  have hdet : A.det = b j₀ := by
    rw [hA, Matrix.det_transpose, ← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hU : IsUnit A.det := by rw [hdet]; exact isUnit_iff_ne_zero.2 hj₀'
  have hAU : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hU
  have hrow : ∀ l, A j₀ l = b l := by
    intro l; simp [hA, Matrix.transpose_apply]
  have hE : Aᴴ * Matrix.single j₀ j₀ (1 : ℂ) * A = Matrix.vecMulVec (star b) b := by
    ext i l
    rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
    · rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
      · simp [hrow, Matrix.vecMulVec_apply]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · intro x _ hx
      have : (Aᴴ * Matrix.single j₀ j₀ (1 : ℂ)) i x = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun y _ => ?_
        simp [Ne.symm hx]
      rw [this, zero_mul]
    · simp
  have : (volume : Measure (Q → Q → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure (fun _ : Q => (volume : Measure (Q → ℂ)))
  obtain ⟨c, hc⟩ := lin_subst (volume : Measure (Q → Q → ℂ)) _ _ (rmulL_comp A A⁻¹ (Matrix.nonsing_inv_mul A hU))
  refine (hc (fun X => G₀ (gram X - Matrix.vecMulVec (star b) b)) (meas_gram_sub G₀ hG _)).trans
    (Eq.trans ?_ (hc (fun X => G₀ (gram X)) (meas_gram G₀ hG)).symm)
  congr 1
  let G₁ : (Q → Q → ℂ) → ℝ≥0∞ := fun T => G₀ (Aᴴ * (Matrix.of T) * A)
  have hG₁ : Measurable G₁ := by
    refine hG.comp (Continuous.measurable ?_)
    exact ((continuous_const (y := Aᴴ)).matrix_mul (continuous_id (X := Matrix Q Q ℂ))).matrix_mul continuous_const
  have h0₁ : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₁ T = 0 := by
    intro T hT
    refine h0 _ fun hP => hT ?_
    exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hAU).1 hP
  have := rank_one_std G₁ hG₁ h0₁ j₀
  have e1 : ∀ X : Q → Q → ℂ, G₀ (gram (rmulL A X) - Matrix.vecMulVec (star b) b) = G₁ (gram X - Matrix.single j₀ j₀ (1 : ℂ)) := by
    intro X
    show _ = G₀ (Aᴴ * (gram X - Matrix.single j₀ j₀ (1 : ℂ)) * A)
    rw [gram_rmulL, Matrix.mul_sub, Matrix.sub_mul, hE]
  have e2 : ∀ X : Q → Q → ℂ, G₀ (gram (rmulL A X)) = G₁ (gram X) := by
    intro X
    show _ = G₀ (Aᴴ * gram X * A)
    rw [gram_rmulL]
  simp_rw [e1, e2]
  exact this

end rankone2

section shearsec

variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]

lemma shear_finset (B : Matrix P Q ℂ) (s : Finset P) :
    ∀ (G₀ : (Q → Q → ℂ) → ℝ≥0∞), Measurable G₀ → (∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0) →
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - ∑ i ∈ s, Matrix.vecMulVec (star (B i)) (B i)) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro G₀ _ _; simp
  | insert a s ha ih =>
    intro G₀ hG h0
    set C : Matrix Q Q ℂ := ∑ i ∈ s, Matrix.vecMulVec (star (B i)) (B i) with hC
    have hCpsd : C.PosSemidef := Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_vecMulVec_star_self (B i)
    let G₁ : (Q → Q → ℂ) → ℝ≥0∞ := fun T => G₀ ((Matrix.of T : Matrix Q Q ℂ) - C)
    have hG₁ : Measurable G₁ := by
      refine hG.comp (Continuous.measurable ?_)
      exact (continuous_id (X := Matrix Q Q ℂ)).sub continuous_const
    have h0₁ : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₁ T = 0 := by
      intro T hT
      refine h0 _ fun hP => hT ?_
      have hP' : (T - C).PosDef := hP
      have := hP'.add_posSemidef hCpsd
      rwa [sub_add_cancel] at this
    have h1 := rank_one G₁ hG₁ h0₁ (B a)
    have h2 := ih G₀ hG h0
    rw [Finset.sum_insert ha]
    have e1 : ∀ X : Q → Q → ℂ, G₀ (gram X - (Matrix.vecMulVec (star (B a)) (B a) + C)) =
        G₁ (gram X - Matrix.vecMulVec (star (B a)) (B a)) := by
      intro X
      show _ = G₀ (gram X - Matrix.vecMulVec (star (B a)) (B a) - C)
      rw [sub_sub]
    exact (lintegral_congr e1).trans (h1.trans h2)

theorem shear (B : Matrix P Q ℂ) (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀)
    (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0) :
    ∫⁻ X : Q → Q → ℂ, G₀ ((cm X)ᴴ * cm X - Bᴴ * B) = ∫⁻ X : Q → Q → ℂ, G₀ ((cm X)ᴴ * cm X) := by
  have hB : Bᴴ * B = ∑ i, Matrix.vecMulVec (star (B i)) (B i) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.sum_apply]
    rfl
  rw [hB]
  exact shear_finset B Finset.univ G₀ hG h0

end shearsec

end Shear

section Core
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}

theorem mp_vec (g : Matrix m m ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun x : m → ℂ => g *ᵥ x) volume volume := by
  have hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h]; norm_num
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (m → ℂ))
    (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h1
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h1
  refine ⟨?_, h1⟩
  exact (LinearMap.continuous_of_finiteDimensional ((Matrix.toLin' g).restrictScalars ℝ)).measurable

theorem mp_cols (g : Matrix m m ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun (Y : Q → m → ℂ) j => g *ᵥ Y j) volume volume :=
  volume_preserving_pi (fun _ => mp_vec g h)

theorem cm_mulVec {n : Type} [Fintype n] (A : Matrix n m ℂ) (Y : Q → m → ℂ) : cm (fun j => A *ᵥ Y j) = A * cm Y := by
  ext i j
  simp only [cm, Matrix.mulVec, Matrix.mul_apply, dotProduct]

theorem map_equiv_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure] (e : E ≃ₗ[ℝ] F) :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map e = c • ν := by
  haveI : (μ.map e).IsAddHaarMeasure := by
    exact e.toContinuousLinearEquiv.isAddHaarMeasure_map μ
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem isAddHaarMeasure_matrix_volume {A B : Type} [Fintype A] [Fintype B] : (volume : Measure (A → B → ℂ)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (B → ℂ)).IsAddHaarMeasure := by
    rw [MeasureTheory.volume_pi]
    first
    | infer_instance
    | exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  rw [MeasureTheory.volume_pi]
  first
  | infer_instance
  | exact MeasureTheory.Measure.pi.isAddHaarMeasure _

attribute [local instance] isAddHaarMeasure_matrix_volume

theorem haar_prod2 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] :
    ((volume : Measure (A → B → ℂ)).prod (volume : Measure (C → D → ℂ))).IsAddHaarMeasure := by
  haveI := (isAddHaarMeasure_matrix_volume : (volume : Measure (A → B → ℂ)).IsAddHaarMeasure)
  haveI := (isAddHaarMeasure_matrix_volume : (volume : Measure (C → D → ℂ)).IsAddHaarMeasure)
  first
  | infer_instance
  | exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

attribute [local instance] haar_prod2

def coordE (F : Frame H Ep Em) : (Q → m → ℂ) ≃ₗ[ℝ] (Q → P → ℂ) × (Q → Q → ℂ) where
  toFun Y := (fun j => Epᴴ *ᵥ Y j, fun j => Emᴴ *ᵥ Y j)
  invFun p := fun j => Ep *ᵥ p.1 j + Em *ᵥ p.2 j
  map_add' Y Y' := by
    ext j i <;> simp [Matrix.mulVec_add]
  map_smul' c Y := by
    ext j i <;> simp [Matrix.mulVec_smul]
  left_inv Y := by
    funext j
    simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, F.sum, Matrix.one_mulVec]
  right_inv p := by
    have hmp : Emᴴ * Ep = 0 := by
      have := congrArg Matrix.conjTranspose F.pm
      simpa using this
    ext j i
    · simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, F.pp, F.pm, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    · simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, F.mm, hmp, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]

theorem coord_meas (F : Frame H Ep Em) : ∃ c : ℝ≥0, 0 < c ∧
    (volume : Measure (Q → m → ℂ)).map (coordE F) = c • ((volume : Measure (Q → P → ℂ)).prod (volume : Measure (Q → Q → ℂ))) := by
  exact map_equiv_smul _ _ (coordE F)

theorem of_cont {A B : Type} : Continuous (fun T : A → B → ℂ => (Matrix.of T : Matrix A B ℂ)) := by
  exact continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)

theorem det_cont : Continuous (fun T : Q → Q → ℂ => (Matrix.of T).det) := by
  exact of_cont.matrix_det

theorem adj_cont : Continuous (fun T : Q → Q → ℂ => (Matrix.of T).adjugate) := by
  exact of_cont.matrix_adjugate

theorem isClosed_posSemidef : IsClosed {T : Q → Q → ℂ | (Matrix.of T).PosSemidef} := by
  have : {T : Q → Q → ℂ | (Matrix.of T).PosSemidef} =
      {T : Q → Q → ℂ | (Matrix.of T)ᴴ = Matrix.of T} ∩ ⋂ x : Q → ℂ, {T : Q → Q → ℂ | 0 ≤ star x ⬝ᵥ (Matrix.of T *ᵥ x)} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [this]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (Continuous.matrix_conjTranspose (continuous_id (X := Matrix Q Q ℂ))) continuous_id
  · refine isClosed_le continuous_const ?_
    exact Continuous.dotProduct continuous_const
      (Continuous.matrix_mulVec (continuous_id (X := Matrix Q Q ℂ)) continuous_const)

theorem measurableSet_posDef : MeasurableSet {T : Q → Q → ℂ | (Matrix.of T).PosDef} := by
  have : {T : Q → Q → ℂ | (Matrix.of T).PosDef} =
      {T : Q → Q → ℂ | (Matrix.of T).PosSemidef} ∩ {T : Q → Q → ℂ | (Matrix.of T).det ≠ 0} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨h.posSemidef, ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero⟩
    · rintro ⟨h1, h2⟩
      exact h1.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h2))
  rw [this]
  refine isClosed_posSemidef.measurableSet.inter ?_
  exact (isOpen_ne_fun det_cont continuous_const).measurableSet

theorem cm_cont {A B : Type} : Continuous (fun Y : B → A → ℂ => cm Y) := by
  exact continuous_matrix fun i j => (continuous_apply i).comp (continuous_apply j)

theorem qf_eq (T : Matrix Q Q ℂ) (B : Matrix P Q ℂ) :
    qf T B = ((T.det)⁻¹ * Matrix.trace (B * T.adjugate * Bᴴ)).re := by
  unfold qf
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem qf_meas : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => qf (Matrix.of p.1) (cm p.2)) := by
  have h : (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => qf (Matrix.of p.1) (cm p.2)) =
      fun p => (((Matrix.of p.1).det)⁻¹ * Matrix.trace (cm p.2 * (Matrix.of p.1).adjugate * (cm p.2)ᴴ)).re :=
    funext fun p => qf_eq _ _
  rw [h]
  have hB : Continuous (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => cm p.2) := cm_cont.comp continuous_snd
  have htr : Continuous (fun p : (Q → Q → ℂ) × (Q → P → ℂ) =>
      Matrix.trace (cm p.2 * (Matrix.of p.1).adjugate * (cm p.2)ᴴ)) :=
    ((hB.matrix_mul (adj_cont.comp continuous_fst)).matrix_mul hB.matrix_conjTranspose).matrix_trace
  exact Complex.measurable_re.comp ((det_cont.comp continuous_fst).measurable.inv.mul htr.measurable)

def Kset (P Q : Type) [Fintype P] [Fintype Q] [DecidableEq Q] (ρ : ℝ) : Set ((Q → Q → ℂ) × (Q → P → ℂ)) :=
  {p | (Matrix.of p.1).PosDef ∧ (Matrix.trace (Matrix.of p.1)).re ≤ 1 ∧ qf (Matrix.of p.1) (cm p.2) ≤ ρ ^ 2}

theorem Kset_meas (ρ : ℝ) : MeasurableSet (Kset P Q ρ) := by
  simp only [Kset, Set.setOf_and]
  have htr : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (Matrix.trace (Matrix.of p.1)).re) :=
    (Complex.continuous_re.comp ((of_cont.comp continuous_fst).matrix_trace)).measurable
  exact (measurable_fst measurableSet_posDef).inter
    ((measurableSet_le htr measurable_const).inter (measurableSet_le qf_meas measurable_const))

def Kf (P Q : Type) [Fintype P] [Fintype Q] [DecidableEq Q] (ρ : ℝ) : (Q → Q → ℂ) × (Q → P → ℂ) → ℝ≥0∞ :=
  (Kset P Q ρ).indicator 1

theorem Kf_meas (ρ : ℝ) : Measurable (Kf P Q ρ) := by
  unfold Kf
  exact measurable_one.indicator (Kset_meas ρ)

def tb (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (Y : Q → m → ℂ) : (Q → Q → ℂ) × (Q → P → ℂ) :=
  (Tm H (cm Y), fun j => Epᴴ *ᵥ Y j)

theorem tb_cont : Continuous (tb H Ep : (Q → m → ℂ) → _) := by
  have h1 : Continuous (fun Y : Q → m → ℂ => (Tm H (cm Y) : Q → Q → ℂ)) := by
    unfold Tm
    exact ((cm_cont.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul cm_cont).neg
  have h2 : Continuous (fun Y : Q → m → ℂ => fun j => Epᴴ *ᵥ Y j) :=
    continuous_pi fun j => continuous_const.matrix_mulVec (continuous_apply j)
  unfold tb
  first
  | exact h1.prodMk h2
  | exact h1.prod_mk h2

def act (g : m → m → ℂ) (Y : Q → m → ℂ) : Q → m → ℂ := fun j => Matrix.of g *ᵥ Y j

theorem act_cont : Continuous (fun p : (m → m → ℂ) × (Q → m → ℂ) => act p.1 p.2) := by
  unfold act
  exact continuous_pi fun j =>
    (of_cont.comp continuous_fst).matrix_mulVec ((continuous_apply j).comp continuous_snd)

def adjF (g : m → m → ℂ) : m → m → ℂ := (Matrix.of g).adjugate

def invF (g : m → m → ℂ) : m → m → ℂ := ((Matrix.of g)⁻¹ : Matrix m m ℂ)

theorem invF_meas : Measurable (invF : (m → m → ℂ) → m → m → ℂ) := by
  have h : (invF : (m → m → ℂ) → m → m → ℂ) =
      fun g => ((((Matrix.of g).det)⁻¹ • (Matrix.of g).adjugate : Matrix m m ℂ) : m → m → ℂ) := by
    funext g
    simp only [invF, Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  rw [h]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact det_cont.measurable.inv.mul (adj_cont.matrix_elem i j).measurable

theorem bet_cont : Continuous (fun g : m → m → ℂ => bet Ep Em (Matrix.of g)) := by
  unfold bet
  have h : Continuous (fun g : m → m → ℂ => Epᴴ * Matrix.of g * Em) :=
    (continuous_const.matrix_mul of_cont).matrix_mul continuous_const
  exact Complex.continuous_re.comp ((h.matrix_mul h.matrix_conjTranspose).matrix_trace)

theorem UH_mul {g h : Matrix m m ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by
    simp only [Matrix.mul_assoc], show gᴴ * H * g = H from hg]
  exact hh

theorem UH_unit (hH : IsUnit H.det) {g : Matrix m m ℂ} (hg : g ∈ UH H) : IsUnit g.det := by
  have h := congrArg Matrix.det (show gᴴ * H * g = H from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h
  exact hH.ne_zero h.symm

theorem UH_inv (hH : IsUnit H.det) {g : Matrix m m ℂ} (hg : g ∈ UH H) : g⁻¹ ∈ UH H := by
  have hu := UH_unit hH hg
  have hg' : gᴴ * H * g = H := hg
  show (g⁻¹)ᴴ * H * g⁻¹ = H
  calc (g⁻¹)ᴴ * H * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * H * (g * g⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def lmF (a : Matrix m m ℂ) (x : m → m → ℂ) : m → m → ℂ := a * Matrix.of x

def rmF (a : Matrix m m ℂ) (x : m → m → ℂ) : m → m → ℂ := Matrix.of x * a

theorem lmF_cont (a : Matrix m m ℂ) : Continuous (lmF a) := by
  unfold lmF
  exact continuous_const.matrix_mul of_cont

theorem rmF_cont (a : Matrix m m ℂ) : Continuous (rmF a) := by
  unfold rmF
  exact of_cont.matrix_mul continuous_const

def Ff (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (ρ : ℝ) (Y : Q → m → ℂ) : ℝ≥0∞ := Kf P Q ρ (tb H Ep Y)

theorem Ff_meas (ρ : ℝ) : Measurable (Ff H Ep ρ : (Q → m → ℂ) → ℝ≥0∞) := by
  unfold Ff
  exact (Kf_meas ρ).comp tb_cont.measurable

def Bset (Ep : Matrix m P ℂ) (Em : Matrix m Q ℂ) (ρ : ℝ) : Set (m → m → ℂ) := {x | bet Ep Em (Matrix.of x) ≤ ρ ^ 2}

theorem Bset_meas (ρ : ℝ) : MeasurableSet (Bset Ep Em ρ) := by
  unfold Bset
  exact measurableSet_le bet_cont.measurable measurable_const

theorem Ff_act (F : Frame H Ep Em) {ρ σ : ℝ} {Y : Q → m → ℂ} (hY : tb H Ep Y ∈ Kset P Q σ) {gY : Matrix m m ℂ}
    {a : Matrix Q Q ℂ} (hgY : gY ∈ UH H) (ha : IsUnit a.det) (hYe : cm Y = gY * Em * a) {g : m → m → ℂ}
    (hg : Matrix.of g ∈ UH H) :
    Ff H Ep ρ (act g Y) = (Bset Ep Em ρ).indicator 1 (rmF gY g) := by
  have e1 : cm (act g Y) = Matrix.of g * cm Y := cm_mulVec _ _
  have e2 : Tm H (cm (act g Y)) = Tm H (cm Y) := by rw [e1, Tm_mul_left hg]
  have e3 : cm (fun j => Epᴴ *ᵥ act g Y j) = Epᴴ * ((Matrix.of g * gY) * Em * a) := by
    rw [cm_mulVec, e1, hYe]; simp only [Matrix.mul_assoc]
  have e4 : Tm H (cm (act g Y)) = Tm H ((Matrix.of g * gY) * Em * a) := by
    rw [e1, hYe]; simp only [Matrix.mul_assoc]
  have key : tb H Ep (act g Y) ∈ Kset P Q ρ ↔ rmF gY g ∈ Bset Ep Em ρ := by
    constructor
    · intro h
      have h3 : qf (Tm H (cm (act g Y))) (cm (fun j => Epᴴ *ᵥ act g Y j)) ≤ ρ ^ 2 := h.2.2
      rw [e3, e4, qf_orbit F (UH_mul hg hgY) ha] at h3
      exact h3
    · intro h
      have h3 : bet Ep Em (Matrix.of g * gY) ≤ ρ ^ 2 := h
      refine ⟨?_, ?_, ?_⟩
      · show (Tm H (cm (act g Y))).PosDef
        rw [e2]; exact hY.1
      · show (Matrix.trace (Tm H (cm (act g Y)))).re ≤ 1
        rw [e2]; exact hY.2.1
      · show qf (Tm H (cm (act g Y))) (cm (fun j => Epᴴ *ᵥ act g Y j)) ≤ ρ ^ 2
        rw [e3, e4, qf_orbit F (UH_mul hg hgY) ha]; exact h3
  by_cases h : rmF gY g ∈ Bset Ep Em ρ
  · rw [Set.indicator_of_mem h]; exact Set.indicator_of_mem (key.mpr h) _
  · rw [Set.indicator_of_notMem h]; exact Set.indicator_of_notMem (fun h' => h (key.mp h')) _

theorem act_meas : Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => act p.1 p.2) := by
  exact act_cont.measurable

theorem act_inv_meas : Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => act (invF p.1) p.2) := by
  have key : ∀ φ : (m → m → ℂ) → m → m → ℂ, Measurable φ →
      Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => act (φ p.1) p.2) := by
    intro φ hφ
    have hp : Measurable (fun p : (m → m → ℂ) × (Q → m → ℂ) => (φ p.1, p.2)) :=
      Measurable.prod (f := fun p : (m → m → ℂ) × (Q → m → ℂ) => (φ p.1, p.2)) (hφ.comp measurable_fst) measurable_snd
    exact act_meas.comp hp
  exact key invF invF_meas

def Lv (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (Q : Type) [Fintype Q] [DecidableEq Q] (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ Y : Q → m → ℂ, Ff H Ep ρ Y

theorem meas_act_left (ρ : ℝ) (Y : Q → m → ℂ) : Measurable fun g : m → m → ℂ => Ff H Ep ρ (act g Y) := by
  unfold act
  exact (Ff_meas ρ).comp (continuous_pi fun j => of_cont.matrix_mulVec continuous_const).measurable

theorem meas_act_inv_left (ρ : ℝ) (Y : Q → m → ℂ) : Measurable fun g : m → m → ℂ => Ff H Ep ρ (act (invF g) Y) := by
  have key : ∀ φ : (m → m → ℂ) → m → m → ℂ, Measurable φ →
      Measurable fun g : m → m → ℂ => Ff H Ep ρ (act (φ g) Y) :=
    fun φ hφ => (meas_act_left ρ Y).comp hφ
  exact key invF invF_meas

theorem meas_act_right (ρ : ℝ) (g : m → m → ℂ) : Measurable fun Y : Q → m → ℂ => Ff H Ep ρ (act g Y) := by
  unfold act
  exact (Ff_meas ρ).comp (continuous_pi fun j => continuous_const.matrix_mulVec (continuous_apply j)).measurable

theorem ind_meas (σ : ℝ) : Measurable ((Bset Ep Em σ).indicator (1 : (m → m → ℂ) → ℝ≥0∞)) := by
  exact measurable_one.indicator (Bset_meas σ)

theorem inner1 (F : Frame H Ep Em) (μ : Measure (m → m → ℂ))
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) (ρ : ℝ) (Y : Q → m → ℂ) :
    ∫⁻ g, Ff H Ep 1 Y * Ff H Ep ρ (act g Y) ∂μ = Ff H Ep 1 Y * μ (Bset Ep Em ρ) := by
  rw [lintegral_const_mul _ (meas_act_left ρ Y)]
  by_cases hY : tb H Ep Y ∈ Kset P Q 1
  · congr 1
    obtain ⟨gY, hgY, a, ha, hYe⟩ := frame_trans F (cm Y) hY.1
    calc ∫⁻ g, Ff H Ep ρ (act g Y) ∂μ
        = ∫⁻ g, (Bset Ep Em ρ).indicator 1 (rmF gY g) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [conc] with g hg
          exact Ff_act F hY hgY ha hYe hg
      _ = ∫⁻ g, (Bset Ep Em ρ).indicator 1 g ∂(μ.map (rmF gY)) :=
          (lintegral_map (ind_meas ρ) (rmF_cont gY).measurable).symm
      _ = μ (Bset Ep Em ρ) := by rw [right gY hgY, lintegral_indicator_one (Bset_meas ρ)]
  · have : Ff H Ep 1 Y = 0 := Set.indicator_of_notMem hY _
    rw [this, zero_mul, zero_mul]

theorem inner2 (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ))
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (ρ : ℝ) (Y : Q → m → ℂ) :
    ∫⁻ g, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y ∂μ = μ (invF ⁻¹' Bset Ep Em 1) * Ff H Ep ρ Y := by
  rw [lintegral_mul_const _ (meas_act_inv_left 1 Y)]
  by_cases hY : tb H Ep Y ∈ Kset P Q ρ
  · congr 1
    obtain ⟨gY, hgY, a, ha, hYe⟩ := frame_trans F (cm Y) hY.1
    have hψ : Measurable (fun g : m → m → ℂ => (Bset Ep Em 1).indicator (1 : (m → m → ℂ) → ℝ≥0∞)
        (rmF gY (invF g))) := (ind_meas 1).comp ((rmF_cont gY).measurable.comp invF_meas)
    calc ∫⁻ g, Ff H Ep 1 (act (invF g) Y) ∂μ
        = ∫⁻ g, (Bset Ep Em 1).indicator 1 (rmF gY (invF g)) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [conc] with g hg
          exact Ff_act F hY hgY ha hYe (UH_inv hH hg)
      _ = ∫⁻ g, (Bset Ep Em 1).indicator 1 (rmF gY (invF g)) ∂(μ.map (lmF gY)) := by rw [left gY hgY]
      _ = ∫⁻ g, (Bset Ep Em 1).indicator 1 (invF g) ∂μ := by
          rw [lintegral_map hψ (lmF_cont gY).measurable]
          refine lintegral_congr fun g => ?_
          congr 1
          show (gY * Matrix.of g)⁻¹ * gY = (Matrix.of g)⁻¹
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (UH_unit hH hgY), Matrix.mul_one]
      _ = μ (invF ⁻¹' Bset Ep Em 1) := by
          rw [← lintegral_indicator_one ((Bset_meas 1).preimage invF_meas)]
          rfl
  · have : Ff H Ep ρ Y = 0 := Set.indicator_of_notMem hY _
    rw [this, mul_zero, mul_zero]

theorem swap_g (hH : IsUnit H.det) (ρ : ℝ) {g : m → m → ℂ} (hg : Matrix.of g ∈ UH H) :
    ∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y) =
      ∫⁻ Y : Q → m → ℂ, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y := by
  have hmp := mp_cols (Q := Q) (Matrix.of g) (det_norm_one hH hg)
  have hfm : Measurable (fun Y : Q → m → ℂ => Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y) :=
    (meas_act_right 1 (invF g)).mul (Ff_meas ρ)
  rw [← hmp.lintegral_comp hfm]
  refine lintegral_congr fun Y => ?_
  have : act (invF g) (fun j => Matrix.of g *ᵥ Y j) = Y := by
    funext j
    show (Matrix.of g)⁻¹ *ᵥ (Matrix.of g *ᵥ Y j) = Y j
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (UH_unit hH hg), Matrix.one_mulVec]
  rw [this]; rfl

theorem eval1 (F : Frame H Ep Em) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) (ρ : ℝ) :
    ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ = Lv H Ep Q 1 * μ (Bset Ep Em ρ) := by
  rw [lintegral_lintegral_swap]
  · simp_rw [inner1 F μ conc right ρ]
    rw [lintegral_mul_const _ (Ff_meas 1)]; rfl
  · refine Measurable.aemeasurable ?_
    exact ((Ff_meas 1).comp measurable_snd).mul ((Ff_meas ρ).comp act_meas)

theorem eval2 (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H) (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (ρ : ℝ) :
    ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ =
      Lv H Ep Q ρ * μ (invF ⁻¹' Bset Ep Em 1) := by
  have s1 : ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 Y * Ff H Ep ρ (act g Y)) ∂μ =
      ∫⁻ g, (∫⁻ Y : Q → m → ℂ, Ff H Ep 1 (act (invF g) Y) * Ff H Ep ρ Y) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [conc] with g hg
    exact swap_g hH ρ hg
  rw [s1, lintegral_lintegral_swap]
  · simp_rw [inner2 F hH μ conc left ρ]
    rw [lintegral_const_mul _ (Ff_meas ρ), mul_comm]; rfl
  · refine Measurable.aemeasurable ?_
    exact ((Ff_meas 1).comp act_inv_meas).mul ((Ff_meas ρ).comp measurable_snd)

theorem trick (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H)
    (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) (ρ : ℝ) :
    Lv H Ep Q 1 * μ (Bset Ep Em ρ) = Lv H Ep Q ρ * μ (invF ⁻¹' Bset Ep Em 1) := by
  rw [← eval1 F μ conc right ρ, eval2 F hH μ conc left ρ]

theorem trace_re {A B : Type} [Fintype A] [Fintype B] (M : Matrix A B ℂ) :
    (Matrix.trace (M * Mᴴ)).re = ∑ i, ∑ j, Complex.normSq (M i j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem cm_smul (c : ℝ) (B : Q → P → ℂ) : cm (c • B) = (c : ℂ) • cm B := by
  ext i j
  simp [cm, Complex.real_smul]

theorem qf_smul (T : Matrix Q Q ℂ) (c : ℝ) (B : Q → P → ℂ) : qf T (cm (c • B)) = c ^ 2 * qf T (cm B) := by
  unfold qf
  rw [cm_smul]
  simp only [Matrix.smul_mul, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, sq]

theorem qf_factor {T a : Matrix Q Q ℂ} (h : T⁻¹ = aᴴ * a) (B : Matrix P Q ℂ) :
    qf T B = ∑ i, ∑ j, Complex.normSq ((B * aᴴ) i j) := by
  unfold qf
  rw [h, show B * (aᴴ * a) * Bᴴ = (B * aᴴ) * (B * aᴴ)ᴴ by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc], trace_re]

theorem qf_definite {T : Matrix Q Q ℂ} (hT : T.PosDef) (B : Matrix P Q ℂ) (h : qf T B ≤ 0) : B = 0 := by
  obtain ⟨a, ha, hTa⟩ := posDef_factor hT.inv
  rw [qf_factor hTa] at h
  have hnn : ∀ i, 0 ≤ ∑ j, Complex.normSq ((B * aᴴ) i j) :=
    fun i => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have h1 : ∑ i, ∑ j, Complex.normSq ((B * aᴴ) i j) = 0 :=
    le_antisymm h (Finset.sum_nonneg fun i _ => hnn i)
  have h0 : B * aᴴ = 0 := by
    ext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp h1 i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp h2 j (Finset.mem_univ _)
    simpa using h3
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  calc B = B * aᴴ * (aᴴ)⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ ha']
    _ = 0 := by rw [h0, Matrix.zero_mul]

theorem qf_zero (T : Matrix Q Q ℂ) : qf T (cm (0 : Q → P → ℂ)) = 0 := by
  have h : cm (0 : Q → P → ℂ) = 0 := by
    ext i j; simp [cm]
  simp [qf, h]

open scoped Pointwise

def Sl (P : Type) [Fintype P] (T : Q → Q → ℂ) (σ : ℝ) : Set (Q → P → ℂ) := {B | qf (Matrix.of T) (cm B) ≤ σ ^ 2}

theorem Sl_meas (T : Q → Q → ℂ) (σ : ℝ) : MeasurableSet (Sl P T σ) := by
  unfold Sl qf
  exact measurableSet_le (Complex.continuous_re.comp
    (((cm_cont.matrix_mul continuous_const).matrix_mul cm_cont.matrix_conjTranspose).matrix_trace)).measurable
    measurable_const

theorem Sl_scale {T : Q → Q → ℂ} (hT : (Matrix.of T).PosDef) {ρ : ℝ} (hρ : 0 ≤ ρ) : Sl P T ρ = ρ • Sl P T 1 := by
  ext B
  rcases hρ.eq_or_lt with h0 | hpos
  · have hne : (Sl P T 1).Nonempty := ⟨0, by simp only [Sl, Set.mem_setOf_eq, qf_zero]; norm_num⟩
    rw [← h0, Set.zero_smul_set hne, Set.mem_zero]
    simp only [Sl, Set.mem_setOf_eq]
    constructor
    · intro h
      have hc : cm B = 0 := qf_definite hT (cm B) (by simpa using h)
      funext j i
      exact congrFun (congrFun hc i) j
    · rintro rfl
      simp [qf_zero]
  · rw [Set.mem_smul_set_iff_inv_smul_mem₀ hpos.ne']
    simp only [Sl, Set.mem_setOf_eq, qf_smul]
    rw [inv_pow, one_pow, inv_mul_le_iff₀ (by positivity), mul_one]

theorem finrank_QP : Module.finrank ℝ (Q → P → ℂ) = 2 * Fintype.card P * Fintype.card Q := by
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  ring

theorem Kf_slice {T : Q → Q → ℂ} (hT : (Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1) (σ : ℝ) :
    (fun B : Q → P → ℂ => Kf P Q σ (T, B)) = (Sl P T σ).indicator 1 := by
  funext B
  by_cases hB : qf (Matrix.of T) (cm B) ≤ σ ^ 2
  · have h1 : (T, B) ∈ Kset P Q σ := by
      simp only [Kset, Set.mem_setOf_eq]; exact ⟨hT.1, hT.2, hB⟩
    have h2 : B ∈ Sl P T σ := by
      simp only [Sl, Set.mem_setOf_eq]; exact hB
    unfold Kf
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    all_goals rfl
  · have h1 : (T, B) ∉ Kset P Q σ := by
      simp only [Kset, Set.mem_setOf_eq]; exact fun h => hB h.2.2
    have h2 : B ∉ Sl P T σ := by
      simp only [Sl, Set.mem_setOf_eq]; exact hB
    unfold Kf
    first
    | rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    | rw [Set.indicator_of_not_mem h1, Set.indicator_of_not_mem h2]

theorem Kf_slice_zero {T : Q → Q → ℂ} (hT : ¬ ((Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1)) (σ : ℝ)
    (B : Q → P → ℂ) : Kf P Q σ (T, B) = 0 := by
  unfold Kf
  rw [Set.indicator_apply_eq_zero]
  intro h
  exact absurd ⟨h.1, h.2.1⟩ hT

theorem slice_scale (T : Q → Q → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ B : Q → P → ℂ, Kf P Q ρ (T, B) =
      ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) * ∫⁻ B : Q → P → ℂ, Kf P Q 1 (T, B) := by
  by_cases hT : (Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1
  · rw [Kf_slice hT, Kf_slice hT, lintegral_indicator_one (Sl_meas T ρ), lintegral_indicator_one (Sl_meas T 1),
      Sl_scale hT.1 hρ, Measure.addHaar_smul, finrank_QP, abs_of_nonneg (pow_nonneg hρ _)]
  · simp [Kf_slice_zero hT]

def gramF (X : Q → Q → ℂ) : Q → Q → ℂ := gram X

def Mv (P Q : Type) [Fintype P] [Fintype Q] [DecidableEq Q] (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ X : Q → Q → ℂ, ∫⁻ B : Q → P → ℂ, Kf P Q ρ (gramF X, B)

theorem Mv_scale {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Mv P Q ρ = ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) * Mv P Q 1 := by
  have hK : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => Kf P Q 1 (gramF p.1, p.2)) := by
    have hg : Measurable (fun X : Q → Q → ℂ => fun i j => gram X i j) :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => (gram_cont.matrix_elem i j).measurable
    have h : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2)) :=
      Measurable.prod (f := fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2)) (hg.comp measurable_fst) measurable_snd
    exact (Kf_meas 1).comp h
  unfold Mv
  simp_rw [slice_scale _ hρ]
  rw [lintegral_const_mul _ hK.lintegral_prod_right']

def swapBlockPair (p : (Q → P → ℂ) × (Q → Q → ℂ)) : (Q → Q → ℂ) × (Q → P → ℂ) :=
  (gram p.2 - (cm p.1)ᴴ * cm p.1, p.1)

theorem k2map_cont : Continuous (swapBlockPair : (Q → P → ℂ) × (Q → Q → ℂ) → (Q → Q → ℂ) × (Q → P → ℂ)) := by
  have hB : Continuous (fun p : (Q → P → ℂ) × (Q → Q → ℂ) => cm p.1) := cm_cont.comp continuous_fst
  have h1 : Continuous (fun p : (Q → P → ℂ) × (Q → Q → ℂ) =>
      ((gram p.2 - (cm p.1)ᴴ * cm p.1 : Matrix Q Q ℂ) : Q → Q → ℂ)) :=
    (gram_cont.comp continuous_snd).sub (hB.matrix_conjTranspose.matrix_mul hB)
  unfold swapBlockPair
  first
  | exact h1.prodMk continuous_fst
  | exact h1.prod_mk continuous_fst

theorem tb_coord (F : Frame H Ep Em) (Y : Q → m → ℂ) : tb H Ep Y = swapBlockPair (coordE F Y) := by
  refine Prod.ext ?_ rfl
  show Tm H (cm Y) = gram (fun j => Emᴴ *ᵥ Y j) - (cm (fun j => Epᴴ *ᵥ Y j))ᴴ * cm (fun j => Epᴴ *ᵥ Y j)
  unfold gram
  rw [cm_mulVec, cm_mulVec, Tm_coord F]

theorem gramF_cont : Continuous (gramF : (Q → Q → ℂ) → Q → Q → ℂ) := by
  exact gram_cont

theorem Kg_meas (ρ : ℝ) : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => Kf P Q ρ (gramF p.1, p.2)) := by
  have h : Measurable (fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2)) :=
    Measurable.prod (f := fun p : (Q → Q → ℂ) × (Q → P → ℂ) => (gramF p.1, p.2))
      (gramF_cont.measurable.comp measurable_fst) measurable_snd
  exact (Kf_meas ρ).comp h

theorem Lv_eq (F : Frame H Ep Em) : ∃ c : ℝ≥0, 0 < c ∧ ∀ ρ : ℝ, Lv H Ep Q ρ = c * Mv P Q ρ := by
  obtain ⟨c, hc, hmap⟩ := coord_meas F
  refine ⟨c, hc, fun ρ => ?_⟩
  have hK : Measurable (fun p : (Q → P → ℂ) × (Q → Q → ℂ) => Kf P Q ρ (swapBlockPair p)) :=
    (Kf_meas ρ).comp k2map_cont.measurable
  have he : Measurable (coordE F) :=
    (LinearMap.continuous_of_finiteDimensional (coordE F).toLinearMap).measurable
  calc Lv H Ep Q ρ = ∫⁻ Y : Q → m → ℂ, Kf P Q ρ (swapBlockPair (coordE F Y)) := by
        unfold Lv Ff; simp_rw [tb_coord F]
    _ = ∫⁻ p, Kf P Q ρ (swapBlockPair p) ∂((volume : Measure (Q → m → ℂ)).map (coordE F)) := (lintegral_map hK he).symm
    _ = c * ∫⁻ p, Kf P Q ρ (swapBlockPair p) ∂((volume : Measure (Q → P → ℂ)).prod (volume : Measure (Q → Q → ℂ))) := by
        rw [hmap, lintegral_smul_measure]; rfl
    _ = c * ∫⁻ B : Q → P → ℂ, ∫⁻ X : Q → Q → ℂ, Kf P Q ρ (swapBlockPair (B, X)) := by
        rw [lintegral_prod _ hK.aemeasurable]
    _ = c * ∫⁻ B : Q → P → ℂ, ∫⁻ X : Q → Q → ℂ, Kf P Q ρ (gramF X, B) := by
        congr 1
        refine lintegral_congr fun B => ?_
        exact shear (cm B) (fun T => Kf P Q ρ (T, B)) ((Kf_meas ρ).comp (measurable_id.prodMk measurable_const))
          (fun T hT => Set.indicator_of_notMem (show ((T : Q → Q → ℂ), B) ∉ Kset P Q ρ from fun h => hT h.1) _)
    _ = c * Mv P Q ρ := by
        rw [lintegral_lintegral_swap]
        · rfl
        · exact ((Kg_meas ρ).comp measurable_swap).aemeasurable

theorem entry_bound (C : Matrix P Q ℂ) (M : Matrix Q Q ℂ) (hC : ∑ i, ∑ j, Complex.normSq (C i j) ≤ 1)
    (hM : ∑ i, ∑ j, Complex.normSq (M i j) ≤ 1) (i : P) (j : Q) : ‖(C * M) i j‖ ≤ 1 := by
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.normSq z := fun z => by
    first
    | exact Complex.sq_norm z
    | exact (Complex.normSq_eq_norm_sq z).symm
  have hC' : ∑ l, ‖C i l‖ ^ 2 ≤ 1 := by
    rw [Finset.sum_congr rfl fun l _ => hn (C i l)]
    exact le_trans (Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (C i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i)) hC
  have hM' : ∑ l, ‖M l j‖ ^ 2 ≤ 1 := by
    rw [Finset.sum_congr rfl fun l _ => hn (M l j)]
    exact le_trans (Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun j => Complex.normSq (M l j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)) hM
  have hx : ‖(C * M) i j‖ ≤ ∑ l, ‖C i l‖ * ‖M l j‖ := by
    rw [Matrix.mul_apply]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖C i l‖) (fun l => ‖M l j‖)
  have h0a : 0 ≤ ∑ l, ‖C i l‖ ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have h0b : 0 ≤ ∑ l, ‖M l j‖ ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hx0 : 0 ≤ ∑ l, ‖C i l‖ * ‖M l j‖ :=
    Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : (∑ l, ‖C i l‖ * ‖M l j‖) ^ 2 ≤ 1 := hcs.trans (by nlinarith)
  have hle : ∑ l, ‖C i l‖ * ‖M l j‖ ≤ 1 := by nlinarith
  exact hx.trans hle

theorem gram_trace (X : Q → Q → ℂ) : (Matrix.trace (gram X)).re = ∑ i, ∑ j, Complex.normSq (X i j) := by
  unfold gram
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, cm, Complex.re_sum,
    Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

theorem gram_unit {X : Q → Q → ℂ} (h : (gram X).PosDef) : IsUnit (cm X).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := h.det_pos
  unfold gram at hd
  rw [Matrix.det_mul, h0, mul_zero] at hd
  exact lt_irrefl _ hd

theorem Kset_bound {X : Q → Q → ℂ} {B : Q → P → ℂ} (h : (gramF X, B) ∈ Kset P Q 1) : ‖(X, B)‖ ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1' : (gram X).PosDef := h1
  have h2' : (Matrix.trace (gram X)).re ≤ 1 := h2
  have h3' : qf (gram X) (cm B) ≤ 1 ^ 2 := h3
  rw [gram_trace] at h2'
  have hu := gram_unit h1'
  have hinv : (gram X)⁻¹ = (((cm X)⁻¹)ᴴ)ᴴ * ((cm X)⁻¹)ᴴ := by
    rw [gram, Matrix.mul_inv_rev, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv]
  rw [qf_factor hinv, Matrix.conjTranspose_conjTranspose, one_pow] at h3'
  have hM : ∑ i, ∑ j, Complex.normSq (cm X i j) ≤ 1 := by
    rw [Finset.sum_comm]; exact h2'
  have hB : ∀ i j, ‖B j i‖ ≤ 1 := by
    intro i j
    have := entry_bound _ _ h3' hM i j
    rwa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at this
  have hX : ∀ i j, ‖X i j‖ ≤ 1 := by
    intro i j
    have e1 : Complex.normSq (X i j) ≤ 1 := by
      refine le_trans ?_ h2'
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (X i j))
        (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => Complex.normSq (X i j)) (fun j _ => Complex.normSq_nonneg _)
        (Finset.mem_univ j)
    rw [Complex.normSq_eq_norm_sq] at e1
    nlinarith [norm_nonneg (X i j)]
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => hX i j
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => hB i j

theorem Mv_lt_top : Mv P Q 1 < ∞ := by
  have e : Mv P Q 1 = ∫⁻ p, Kf P Q 1 (gramF p.1, p.2)
      ∂((volume : Measure (Q → Q → ℂ)).prod (volume : Measure (Q → P → ℂ))) := by
    rw [lintegral_prod _ (Kg_meas 1).aemeasurable]; rfl
  rw [e]
  have hle : ∀ p : (Q → Q → ℂ) × (Q → P → ℂ), Kf P Q 1 (gramF p.1, p.2) ≤
      (Metric.closedBall (0 : (Q → Q → ℂ) × (Q → P → ℂ)) 1).indicator 1 p := by
    intro p
    by_cases h : (gramF p.1, p.2) ∈ Kset P Q 1
    · have : p ∈ Metric.closedBall (0 : (Q → Q → ℂ) × (Q → P → ℂ)) 1 := by
        rw [mem_closedBall_zero_iff]; exact Kset_bound h
      rw [Set.indicator_of_mem this]
      exact le_of_eq (Set.indicator_of_mem h _)
    · have : Kf P Q 1 (gramF p.1, p.2) = 0 := Set.indicator_of_notMem h _
      rw [this]; exact zero_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
  exact (isCompact_closedBall _ _).measure_lt_top

theorem qfT_cont (T : Matrix Q Q ℂ) : Continuous (fun B : Q → P → ℂ => qf T (cm B)) := by
  unfold qf
  exact Complex.continuous_re.comp
    (((cm_cont.matrix_mul continuous_const).matrix_mul cm_cont.matrix_conjTranspose).matrix_trace)

theorem slice_pos {T : Q → Q → ℂ} (hT : (Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1) :
    0 < ∫⁻ B : Q → P → ℂ, Kf P Q 1 (T, B) := by
  rw [Kf_slice hT, lintegral_indicator_one (Sl_meas T 1)]
  have hopen : IsOpen {B : Q → P → ℂ | qf (Matrix.of T) (cm B) < 1} :=
    isOpen_lt (qfT_cont _) continuous_const
  have hne : {B : Q → P → ℂ | qf (Matrix.of T) (cm B) < 1}.Nonempty :=
    ⟨0, by show qf _ _ < 1; rw [qf_zero]; norm_num⟩
  refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono ?_)
  intro B hB
  have hB' : qf (Matrix.of T) (cm B) < 1 := hB
  show qf _ _ ≤ _
  rw [one_pow]; exact hB'.le

theorem Mv_pos : 0 < Mv P Q 1 := by
  have hf : Measurable (fun X : Q → Q → ℂ => ∫⁻ B : Q → P → ℂ, Kf P Q 1 (gramF X, B)) :=
    (Kg_meas 1).lintegral_prod_right'
  unfold Mv
  rw [lintegral_pos_iff_support hf]
  have hopen : IsOpen {X : Q → Q → ℂ | (cm X).det ≠ 0 ∧ (Matrix.trace (gram X)).re < 1} := by
    have o1 : IsOpen {X : Q → Q → ℂ | (cm X).det ≠ 0} :=
      isOpen_ne_fun (Continuous.matrix_det cm_cont) continuous_const
    have o2 : IsOpen {X : Q → Q → ℂ | (Matrix.trace (gram X)).re < 1} :=
      isOpen_lt (Complex.continuous_re.comp (Continuous.matrix_trace
        (Continuous.matrix_mul (Continuous.matrix_conjTranspose cm_cont) cm_cont))) continuous_const
    exact o1.inter o2
  have hne : {X : Q → Q → ℂ | (cm X).det ≠ 0 ∧ (Matrix.trace (gram X)).re < 1}.Nonempty := by
    set c : ℝ := 1 / ((Fintype.card Q : ℝ) + 1) with hc
    have hc0 : 0 < c := by positivity
    refine ⟨fun i j => if i = j then (c : ℂ) else 0, ?_, ?_⟩
    · have : cm (fun i j : Q => if i = j then (c : ℂ) else 0) = (c : ℂ) • (1 : Matrix Q Q ℂ) := by
        ext i j
        show (if j = i then (c : ℂ) else 0) = ((c : ℂ) • (1 : Matrix Q Q ℂ)) i j
        simp [Matrix.one_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc0.ne')
    · rw [gram_trace]
      have : ∀ i : Q, ∑ j, Complex.normSq (if i = j then (c : ℂ) else 0) = c ^ 2 := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp [Complex.normSq_ofReal, sq]
        · intro j _ hj
          simp [hj.symm]
        · intro h; exact absurd (Finset.mem_univ i) h
      simp_rw [this]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
      have hq : (0 : ℝ) ≤ Fintype.card Q := Nat.cast_nonneg _
      rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
      nlinarith
  refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono ?_)
  rintro X ⟨h1, h2⟩
  have hpd : (gram X).PosDef := by
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h1))
  exact (slice_pos (P := P) (T := gramF X) ⟨hpd, h2.le⟩).ne'

theorem vol_core (F : Frame H Ep Em) (hH : IsUnit H.det) (μ : Measure (m → m → ℂ)) [SFinite μ]
    (conc : ∀ᵐ g ∂μ, Matrix.of g ∈ UH H)
    (left : ∀ a ∈ UH H, μ.map (lmF a) = μ) (right : ∀ a ∈ UH H, μ.map (rmF a) = μ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    μ (Bset Ep Em ρ) = μ (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q)) := by
  obtain ⟨c, hc, hL⟩ := Lv_eq F
  have h := trick F hH μ conc left right ρ
  rw [hL 1, hL ρ, Mv_scale hρ] at h
  have hne : (c : ℝ≥0∞) * Mv P Q 1 ≠ 0 := mul_ne_zero (ENNReal.coe_ne_zero.mpr hc.ne') Mv_pos.ne'
  have hnt : (c : ℝ≥0∞) * Mv P Q 1 ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top Mv_lt_top.ne
  have h' : (c : ℝ≥0∞) * Mv P Q 1 * μ (Bset Ep Em ρ) = (c : ℝ≥0∞) * Mv P Q 1 *
      (μ (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * Fintype.card P * Fintype.card Q))) := by
    rw [h]; ring
  exact (ENNReal.mul_right_inj hne hnt).mp h'

theorem gN_sq' {k r : ℕ} (A : Mat k r) : gN A ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [gN_sq, trace_re]

theorem ball_bound {k r : ℕ} {c : ℝ} (hc : 1 ≤ c) {g : Mt k r} (h : gN (Matrix.of g) ^ 2 ≤ c) : ‖g‖ ≤ c := by
  have hc0 : 0 ≤ c := by linarith
  rw [gN_sq'] at h
  refine (pi_norm_le_iff_of_nonneg hc0).2 fun i => (pi_norm_le_iff_of_nonneg hc0).2 fun j => ?_
  have h1 : Complex.normSq (g i j) ≤ ∑ i, ∑ j, Complex.normSq (Matrix.of g i j) :=
    le_trans (Finset.single_le_sum (f := fun j => Complex.normSq (Matrix.of g i j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Matrix.of g i j))
        (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
  have h2 : ‖g i j‖ ^ 2 ≤ c := by
    have h3 : ‖g i j‖ ^ 2 = Complex.normSq (g i j) := by
      first
      | exact Complex.sq_norm _
      | exact (Complex.normSq_eq_norm_sq _).symm
    rw [h3]; linarith
  nlinarith [norm_nonneg (g i j), mul_le_mul_of_nonneg_left hc hc0]

theorem volExact : VolExact := by
  intro k r μG hμ
  obtain ⟨Ep, Em, F⟩ := frame_exists k r
  have hH : IsUnit (Hpk k r).det := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hdet k r
  have : IsFiniteMeasureOnCompacts μG := ⟨fun K hK => hμ.finite_compact K hK⟩
  have conc : ∀ᵐ g ∂μG, Matrix.of g ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.conc
  have left : ∀ a ∈ UH (Hpk k r), μG.map (lmF a) = μG := fun a ha => hμ.left a ha
  have right : ∀ a ∈ UH (Hpk k r), μG.map (rmF a) = μG := fun a ha => hμ.right a ha
  have hset : ∀ ρ : ℝ, μG {g | gN (Matrix.of g) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) + 4 * ρ ^ 2} = μG (Bset Ep Em ρ) := by
    intro ρ
    refine measure_congr ?_
    filter_upwards [conc] with g hg
    have e1 := hsblock k r (Matrix.of g) hg
    have e2 := bet_eq F (Matrix.of g)
    refine propext ?_
    show gN (Matrix.of g) ^ 2 ≤ _ ↔ bet Ep Em (Matrix.of g) ≤ ρ ^ 2
    rw [e1, e2]
    constructor <;> intro h <;> linarith
  have hV : ∀ ρ : ℝ, 0 ≤ ρ → μG (Bset Ep Em ρ) =
      μG (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * (k + r) * (r + 1))) := by
    intro ρ hρ
    have := vol_core F hH μG conc left right hρ
    rwa [Fintype.card_fin, Fintype.card_fin] at this
  have hV1 : μG (invF ⁻¹' Bset Ep Em 1) = μG (Bset Ep Em 1) := by
    have := hV 1 zero_le_one
    rw [one_pow, ENNReal.ofReal_one, mul_one] at this
    exact this.symm
  have hfin : μG (invF ⁻¹' Bset Ep Em 1) ≠ ∞ := by
    rw [hV1, ← hset 1]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (hμ.finite_compact _ (isCompact_closedBall (0 : Mt k r) (((2 * r + k + 1 : ℕ) : ℝ) + 4 * 1 ^ 2))))
    intro g hg
    rw [mem_closedBall_zero_iff]
    refine ball_bound ?_ hg
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hpos : μG (invF ⁻¹' Bset Ep Em 1) ≠ 0 := by
    intro h0
    apply hμ.ne_zero
    have hun : (Set.univ : Set (Mt k r)) = ⋃ N : ℕ, Bset Ep Em (N : ℝ) := by
      symm
      rw [Set.eq_univ_iff_forall]
      intro g
      obtain ⟨N, hN⟩ := exists_nat_ge (bet Ep Em (Matrix.of g))
      refine Set.mem_iUnion.mpr ⟨N + 1, ?_⟩
      show bet Ep Em (Matrix.of g) ≤ ((N + 1 : ℕ) : ℝ) ^ 2
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      push_cast
      nlinarith
    have : μG Set.univ = 0 := by
      rw [hun]
      refine measure_iUnion_null fun N => ?_
      rw [hV N (Nat.cast_nonneg _), h0, zero_mul]
    exact Measure.measure_univ_eq_zero.mp this
  refine ⟨(μG (invF ⁻¹' Bset Ep Em 1)).toNNReal, ENNReal.toNNReal_pos hpos hfin, fun ρ hρ => ?_⟩
  rw [hset ρ, hV ρ hρ, ENNReal.coe_toNNReal hfin]

theorem volSharp : VolSharp := by
  intro k r μG hμ
  obtain ⟨C, -, hC⟩ := volExact k r μG hμ
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hsub : {g : Mt k r | gN (Matrix.of g) ≤ R} ⊆
      {g | gN (Matrix.of g) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) + 4 * R ^ 2} := by
    intro g hg
    have h0 : 0 ≤ gN (Matrix.of g) := Real.sqrt_nonneg _
    have h1 : gN (Matrix.of g) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hg 2
    have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    show gN (Matrix.of g) ^ 2 ≤ _
    nlinarith [sq_nonneg R]
  refine (measure_mono hsub).trans ?_
  rw [hC R hR0]
  have e : R ^ (2 * ((k : ℝ) + r) * ((r : ℝ) + 1)) = R ^ (2 * (k + r) * (r + 1)) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [e, ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end Core

end Formalism.FourierDecayAlt.P.HermitianFormFactor

namespace Formalism.FourierDecayAlt.P

theorem normalisation_every_setting : Formalism.FourierDecayAlt.B2.IntNormBFromNorm := fun h k r _ _ _ _ _ _ D =>
  h k r D.z D.z' D.μsec D.μG D.μW D.μN D.μW'
    ⟨D.k_pos, D.z_mem, D.z'_mem, D.T_pos, D.T'_pos, D.haarG, D.haarW, D.haarN, D.haarW', D.sec⟩

theorem matrix_norm_ge_one : Formalism.FourierDecayAlt.B2.GNLower := by
  intro k r g hg
  have h := HermitianFormFactor.hsblock k r g hg
  have h0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have h1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := Nat.le_add_left 1 _
    exact_mod_cast this
  nlinarith [sq_nonneg (B.gN (B2.Ppos k r * g * B2.Pneg k r))]

theorem hilbert_schmidt_block : Formalism.FourierDecayAlt.B2.HSBlock := by
  exact HermitianFormFactor.hsblock

theorem norm_ball_volume_exact : Formalism.FourierDecayAlt.B2.VolExact := by
  exact HermitianFormFactor.volExact

theorem norm_ball_volume_sharp : Formalism.FourierDecayAlt.B2.VolSharp := by
  exact HermitianFormFactor.volSharp

end Formalism.FourierDecayAlt.P
