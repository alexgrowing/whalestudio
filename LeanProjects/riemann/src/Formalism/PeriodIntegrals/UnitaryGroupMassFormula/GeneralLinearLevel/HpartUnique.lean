import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearLevel.ExpMulVecFix
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FinalIO

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.EabGlW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hsq : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1

lemma hsq' (M : Mx k r) : Hpk k r * (Hpk k r * M) = M := by
  rw [← Matrix.mul_assoc, hsq, Matrix.one_mul]

lemma hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hsq

def Skew (X : Mx k r) : Prop := Xᴴ * Hpk k r + Hpk k r * X = 0

def LieL (k r : ℕ) (i : Fin (r + 1)) : Set (Mx k r) :=
  {X | Skew X ∧ ∀ a : Fin r, a.val < i.val →
    X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0}

def Out (k r : ℕ) (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop :=
  p.val < i.val ∨ 2 * r + k - i.val < p.val

def InV (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  ∀ p q : Fin (2 * r + k + 1), (Out k r i p ∨ Out k r i q) → Z p q = 0

lemma skew_conj {X : Mx k r} (h : Skew X) : Xᴴ = Hpk k r * (-X) * Hpk k r := by
  have h' : Xᴴ * Hpk k r + Hpk k r * X = 0 := h
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left h'
  calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hsq, Matrix.mul_one]
    _ = -(Hpk k r * X) * Hpk k r := by rw [h1]
    _ = Hpk k r * (-X) * Hpk k r := by rw [Matrix.mul_neg, Matrix.neg_mul]

lemma exp_uh {X : Mx k r} (h : Skew X) : NormedSpace.exp X ∈ UH (Hpk k r) := by
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hsq)
  have hc := Matrix.exp_conj (Hpk k r) (-X) hU
  rw [hinv] at hc
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  rw [← Matrix.exp_conjTranspose, skew_conj h, hc,
    Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-X)) (Hpk k r) (Hpk k r), hsq, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

lemma lieL_rsmul {i : Fin (r + 1)} {X : Mx k r} (hX : X ∈ LieL k r i) (t : ℝ) :
    (t : ℂ) • X ∈ LieL k r i := by
  obtain ⟨h1, h2⟩ := hX
  have h1' : Xᴴ * Hpk k r + Hpk k r * X = 0 := h1
  refine ⟨?_, fun a ha => ?_⟩
  · show ((t : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((t : ℂ) • X) = 0
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, h1', smul_zero]
  · obtain ⟨e1, e2⟩ := h2 a ha
    exact ⟨by rw [Matrix.smul_mulVec, e1, smul_zero],
      by rw [Matrix.smul_mulVec, e2, smul_zero]⟩

theorem flow_of_lieL {i : Fin (r + 1)} {X : Mx k r} (hX : X ∈ LieL k r i) : Flow (Glev k r i) X := by
  intro g hg t
  have hY : (t : ℂ) • X ∈ LieL k r i := lieL_rsmul hX t
  obtain ⟨hgU, hgv⟩ := hg
  have hgU' : gᴴ * Hpk k r * g = Hpk k r := hgU
  have hE' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r :=
    exp_uh hY.1
  refine ⟨?_, fun a ha => ?_⟩
  · show (g * NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * (g * NormedSpace.exp ((t : ℂ) • X)) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc _ = (NormedSpace.exp ((t : ℂ) • X))ᴴ * (gᴴ * Hpk k r * g) * NormedSpace.exp ((t : ℂ) • X) := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hgU', hE']
  · obtain ⟨e1, e2⟩ := hY.2 a ha
    obtain ⟨g1, g2⟩ := hgv a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ _ e1, g1],
      by rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ _ e2, g2]⟩

lemma lieL_add {i : Fin (r + 1)} {X Y : Mx k r} (hX : X ∈ LieL k r i) (hY : Y ∈ LieL k r i) :
    X + Y ∈ LieL k r i := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  have a1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX1
  have b1 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY1
  refine ⟨?_, fun a ha => ?_⟩
  · show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [a1, b1, add_zero]
  · obtain ⟨x1, x2⟩ := hX2 a ha
    obtain ⟨y1, y2⟩ := hY2 a ha
    exact ⟨by rw [Matrix.add_mulVec, x1, y1, add_zero], by rw [Matrix.add_mulVec, x2, y2, add_zero]⟩

lemma lieL_sub {i : Fin (r + 1)} {X Y : Mx k r} (hX : X ∈ LieL k r i) (hY : Y ∈ LieL k r i) :
    X - Y ∈ LieL k r i := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  have a1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX1
  have b1 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY1
  refine ⟨?_, fun a ha => ?_⟩
  · show (X - Y)ᴴ * Hpk k r + Hpk k r * (X - Y) = 0
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) - (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [a1, b1, sub_zero]
  · obtain ⟨x1, x2⟩ := hX2 a ha
    obtain ⟨y1, y2⟩ := hY2 a ha
    exact ⟨by rw [Matrix.sub_mulVec, x1, y1, sub_zero], by rw [Matrix.sub_mulVec, x2, y2, sub_zero]⟩

lemma lieL_bracket {i : Fin (r + 1)} {X Y : Mx k r} (hX : X ∈ LieL k r i) (hY : Y ∈ LieL k r i) :
    X * Y - Y * X ∈ LieL k r i := by
  have cX := skew_conj hX.1
  have cY := skew_conj hY.1
  refine ⟨?_, fun a ha => ?_⟩
  · show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, cX, cY]
    simp only [Matrix.mul_assoc, hsq', hsq, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.sub_mul, Matrix.mul_sub]
    all_goals abel
  · obtain ⟨x1, x2⟩ := hX.2 a ha
    obtain ⟨y1, y2⟩ := hY.2 a ha
    exact ⟨by rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, y1, x1,
        Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero],
      by rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, y2, x2,
        Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]⟩

lemma skew_hpart1 (Z : Mx k r) : Skew (hpart1 (Hpk k r) Z) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    first | simp | (rw [Complex.star_def]; simp)
  show (hpart1 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) Z = 0
  simp only [hpart1, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  all_goals module

lemma skew_hpart2 (Z : Mx k r) : Skew (hpart2 (Hpk k r) Z) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    ring
  show (hpart2 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart2 (Hpk k r) Z = 0
  simp only [hpart2, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  all_goals module

lemma mulVec_bvec (M : Mx k r) (q : Fin (2 * r + k + 1)) : M *ᵥ bvec q = fun p => M p q := by
  funext p
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma out_of_sig {i : Fin (r + 1)} {q v : Fin (2 * r + k + 1)} (hq : Out k r i q)
    (hv : q = GBasic.sig k r v) : Out k r i v := by
  subst hv
  have := i.isLt
  have := v.isLt
  unfold Out at hq ⊢
  unfold GBasic.sig at hq
  split_ifs at hq with h
  · rcases hq with hq | hq <;> (try simp only [Fin.val_mk] at hq) <;> omega
  · exact hq

lemma col_HZH {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) {q : Fin (2 * r + k + 1)}
    (hq : Out k r i q) (p : Fin (2 * r + k + 1)) : (Hpk k r * Zᴴ * Hpk k r) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : Out k r i b
  · have h0 : (Hpk k r * Zᴴ) p b = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      rw [Matrix.conjTranspose_apply, hZ b a (Or.inl hb), star_zero, mul_zero]
    rw [h0, zero_mul]
  · have h0 : Hpk k r b q = 0 := by
      unfold Out at hq hb
      have := i.isLt
      have := b.isLt
      have := q.isLt
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    rw [h0, mul_zero]

lemma hpart_kill {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) {q : Fin (2 * r + k + 1)}
    (hq : Out k r i q) :
    hpart1 (Hpk k r) Z *ᵥ bvec q = 0 ∧ hpart2 (Hpk k r) Z *ᵥ bvec q = 0 := by
  rw [mulVec_bvec, mulVec_bvec]
  refine ⟨funext fun p => ?_, funext fun p => ?_⟩ <;>
    simp only [hpart1, hpart2, hinv, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      hZ p q (Or.inr hq), col_HZH hZ hq p, sub_zero, add_zero, smul_zero, Pi.zero_apply]

lemma out_eI {i : Fin (r + 1)} (a : Fin r) (ha : a.val < i.val) : Out k r i (eI k r a) := by
  exact Or.inl ha

lemma out_esI {i : Fin (r + 1)} (a : Fin r) (ha : a.val < i.val) : Out k r i (esI k r a) := by
  have := i.isLt
  have := a.isLt
  right
  show 2 * r + k - i.val < 2 * r + k - a.val
  omega

theorem hpart_mem {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) :
    hpart1 (Hpk k r) Z ∈ LieL k r i ∧ hpart2 (Hpk k r) Z ∈ LieL k r i :=
  ⟨⟨skew_hpart1 Z, fun a ha => ⟨(hpart_kill hZ (out_eI a ha)).1, (hpart_kill hZ (out_esI a ha)).1⟩⟩,
    ⟨skew_hpart2 Z, fun a ha => ⟨(hpart_kill hZ (out_eI a ha)).2, (hpart_kill hZ (out_esI a ha)).2⟩⟩⟩

lemma hpart_decomp (Z : Mx k r) : Z = hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
    try ring
  unfold hpart1 hpart2
  rw [smul_smul, hI]
  module

lemma hpart_unique {P Q : Mx k r} (hP : Skew P) (hQ : Skew Q) :
    hpart1 (Hpk k r) (P + Complex.I • Q) = P ∧ hpart2 (Hpk k r) (P + Complex.I • Q) = Q := by
  have hWP : Hpk k r * Pᴴ * Hpk k r = -P := by
    rw [skew_conj hP]
    simp only [Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  have hWQ : Hpk k r * Qᴴ * Hpk k r = -Q := by
    rw [skew_conj hQ]
    simp only [Matrix.mul_assoc, hsq', hsq, Matrix.mul_one]
  have hW : Hpk k r * (P + Complex.I • Q)ᴴ * Hpk k r = -P + Complex.I • Q := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hWP, hWQ, Complex.star_def, Complex.conj_I, neg_smul,
      smul_neg, neg_neg]
  have hI : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by
    have := Complex.I_ne_zero
    field_simp
  unfold hpart1 hpart2
  rw [hinv, hW]
  constructor
  · rw [show P + Complex.I • Q - (-P + Complex.I • Q) = (2 : ℂ) • P by module, smul_smul]
    norm_num
  · rw [show P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q by module, smul_smul, hI,
      one_smul]

end Formalism.FourierDecayAlt.Q.EabGlW
