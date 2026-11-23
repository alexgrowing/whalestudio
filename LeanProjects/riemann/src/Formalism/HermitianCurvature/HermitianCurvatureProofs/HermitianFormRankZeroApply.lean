import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.Ux2
open scoped ComplexConjugate

noncomputable section

section law

variable {k j ρ : ℕ}

def skc (M : Matrix (Fin j) (Fin j) ℂ) : (G.UT j → ℂ) × (Fin j → ℝ) :=
  (fun p => M p.1.1 p.1.2, fun a => (M a a).im)

lemma skewOf_gt (q : (G.UT j → ℂ) × (Fin j → ℝ)) {a b : Fin j} (h : b < a) :
    skewOf q a b = -conj (skewOf q b a) := by
  have := congrFun (congrFun (skewOf_ct q) b) a
  rw [conjTranspose_apply, Matrix.neg_apply] at this
  have h2 : conj (skewOf q a b) = -skewOf q b a := this
  have h3 := congrArg conj h2
  rw [Complex.conj_conj, map_neg] at h3
  exact h3

lemma skewOf_skc {M : Matrix (Fin j) (Fin j) ℂ} (hM : Mᴴ = -M) : skewOf (skc M) = M := by
  have hM' : ∀ a b, conj (M b a) = -M a b := fun a b => by
    have := congrFun (congrFun hM a) b
    rwa [conjTranspose_apply] at this
  ext a b
  rcases lt_trichotomy a b with h | rfl | h
  · rw [skewOf_lt _ h]; rfl
  · rw [skewOf_diag]
    have h1 := hM' a a
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im]
      have := congrArg Complex.re h1
      simp only [Complex.conj_re, Complex.neg_re] at this
      simp [skc]; linarith
    · simp [skc]
  · rw [skewOf_gt _ h, skewOf_lt _ h]
    show -conj (M b a) = M a b
    rw [hM']; ring

lemma skewOf_add (q1 q2 : (G.UT j → ℂ) × (Fin j → ℝ)) : skewOf (q1 + q2) = skewOf q1 + skewOf q2 := by
  ext a b
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [Matrix.add_apply]; rw [skewOf_lt _ h, skewOf_lt _ h, skewOf_lt _ h]; rfl
  · simp only [Matrix.add_apply]; rw [skewOf_diag, skewOf_diag, skewOf_diag]
    simp only [Prod.snd_add, Pi.add_apply, Complex.ofReal_add]; ring
  · simp only [Matrix.add_apply]
    rw [skewOf_gt _ h, skewOf_gt _ h, skewOf_gt _ h, skewOf_lt _ h, skewOf_lt _ h, skewOf_lt _ h]
    simp only [Prod.fst_add, Pi.add_apply, map_add]; ring

def kap (c1 c2 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) : (G.UT j → ℂ) × (Fin j → ℝ) :=
  skc ((1 / 2 : ℂ) • (c2ᴴ * Hpk k ρ * c1 - c1ᴴ * Hpk k ρ * c2))

lemma kap_skew (c1 c2 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    ((1 / 2 : ℂ) • (c2ᴴ * Hpk k ρ * c1 - c1ᴴ * Hpk k ρ * c2))ᴴ =
      -((1 / 2 : ℂ) • (c2ᴴ * Hpk k ρ * c1 - c1ᴴ * Hpk k ρ * c2)) := by
  have hH : (Hpk k ρ)ᴴ = Hpk k ρ := (hpkFacts k ρ).1
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_mul, hH, conjTranspose_conjTranspose, conjTranspose_conjTranspose]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp [Complex.ext_iff]
  rw [hs]
  simp only [Matrix.mul_assoc]
  module

def mulC (x1 x2 : RC k j ρ) : RC k j ρ :=
  (x1.1 + x2.1, x1.2 + x2.2 + kap (Matrix.of x1.1) (Matrix.of x2.1))

theorem rn_mul (x1 x2 : RC k j ρ) : Rn k j ρ x1 * Rn k j ρ x2 = Rn k j ρ (mulC x1 x2) := by
  rw [Ux3.rn_eq, Ux3.rn_eq, Ux3.rn_eq, block3_mul]
  have hof : (Matrix.of (x1.1 + x2.1) : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = Matrix.of x1.1 + Matrix.of x2.1 := rfl
  simp only [mulC, hof, skewOf_add, kap, skewOf_skc (kap_skew _ _)]
  refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (try simp only [hof, conjTranspose_add]) <;>
    simp [-Matrix.of_add_of, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, conjTranspose_add, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul] <;> module

end law

section n0

variable {k r : ℕ}

lemma eB_ll' (a : Fin r) : eB k r 0 (Sum.inl (Sum.inl a)) = eI k r a := by
  ext; rw [eB_ll]; rfl

lemma mulVec_eB (M : B.Mat k (r + 0)) (y : Fin (2 * r + k + 1) → ℂ) (p : Ix k r 0) :
    (M *ᵥ y) (eB k r 0 p) = ∑ q : Ix k r 0, M (eB k r 0 p) (eB k r 0 q) * y (eB k r 0 q) := by
  simp only [Matrix.mulVec, dotProduct]
  exact (Equiv.sum_comp (eB k r 0) (fun q => M (eB k r 0 p) q * y q)).symm

def yb (y : Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * 0 + k + 1)) : ℂ := y (eB k r 0 (Sum.inl (Sum.inr v)))

lemma wb_ll {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) (a : Fin r) : y (eB k r 0 (Sum.inl (Sum.inl a))) = 0 :=
  hy _ (Or.inl (by rw [eB_ll]; exact a.isLt))

lemma wb_r {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) (a : Fin r) : y (eB k r 0 (Sum.inr a)) = 0 :=
  hy _ (Or.inr (by rw [eB_r]; omega))

def a12 (x : RC k r 0) : Matrix (Fin r) (Fin (2 * 0 + k + 1)) ℂ := -(G.wMat r * (Matrix.of x.1)ᴴ * Hpk k 0)

lemma rn_mulVec (x : RC k r 0) {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) :
    (∀ a, (Rn k r 0 x *ᵥ y) (eB k r 0 (Sum.inl (Sum.inl a))) = (a12 x *ᵥ yb y) a) ∧
    (∀ v, (Rn k r 0 x *ᵥ y) (eB k r 0 (Sum.inl (Sum.inr v))) = yb y v) ∧
    (∀ a, (Rn k r 0 x *ᵥ y) (eB k r 0 (Sum.inr a)) = 0) := by
  have key : ∀ p, (Rn k r 0 x *ᵥ y) (eB k r 0 p) =
      ∑ v, Rn k r 0 x (eB k r 0 p) (eB k r 0 (Sum.inl (Sum.inr v))) * yb y v := by
    intro p
    rw [mulVec_eB, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [wb_ll hy, wb_r hy, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    rfl
  refine ⟨fun a => ?_, fun v => ?_, fun a => ?_⟩ <;> rw [key] <;>
    simp [Ux3.rn_eq, block3_apply, a12, Matrix.mulVec, dotProduct, yb, Matrix.one_apply]

lemma rn_col (x : RC k r 0) (b : Fin r) : Rn k r 0 x *ᵥ bvec (eI k r b) = bvec (eI k r b) := by
  have h := (rn_rset x).2.1
  ext i
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h i (eI k r b) (by show b.val < r; exact b.isLt)]

end n0

section coords

variable {k r : ℕ}

lemma hpk_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ z) i = (if r ≤ i.val ∧ i.val ≤ r + k then (if i.val = r + k then -1 else 1) else 0) * z i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [if_pos h]; congr 1; unfold Hpk
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [if_neg h]
      have : z i = 0 := hz i (by omega)
      simp [this]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have : Hpk k r i j = 0 := by
        unfold Hpk
        have hne : i.val ≠ j.val := fun h => hji (Fin.ext h).symm
        split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (exfalso; exact hne (by rw [h3.2.2]))
      simp [this]
    · have : z j = 0 := hz j (by omega)
      simp [this]
  · simp

lemma wb_last_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) :
    z ⟨r + k, by omega⟩ ≠ 0 := by
  intro h0
  have hT := hz.2
  unfold Tz at hT
  have hre : 0 ≤ (herm (Hpk k r) z z).re := by
    unfold herm
    simp only [dotProduct, Pi.star_apply, hpk_mulVec_wb hz.1, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [if_pos h]
      by_cases hl : i.val = r + k
      · have : i = ⟨r + k, by omega⟩ := Fin.ext hl
        rw [this, h0]; simp
      · rw [if_neg hl, one_mul]
        have := Complex.mul_conj' (z i)
        rw [mul_comm] at this
        simp only [RCLike.star_def]
        rw [this]
        exact_mod_cast sq_nonneg ‖z i‖
    · rw [if_neg h]; simp
  linarith

def hb (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * 0 + k + 1) → ℂ := Hpk k 0 *ᵥ yb z

lemma hermitian_form_rank_zero_apply (y : Fin (2 * 0 + k + 1) → ℂ) (v : Fin (2 * 0 + k + 1)) :
    (Hpk k 0 *ᵥ y) v = (if v.val = 0 + k then -1 else 1) * y v := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single v]
  · congr 1; unfold Hpk; have := v.isLt; split_ifs <;> first | rfl | (exfalso; omega)
  · intro j _ hjv
    have : Hpk k 0 v j = 0 := by
      unfold Hpk
      have hne : v.val ≠ j.val := fun h => hjv (Fin.ext h).symm
      split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (exfalso; exact hne (by rw [h3.2.2]))
    simp [this]
  · simp

lemma hb_last_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : hb z (Fin.last (2 * 0 + k)) ≠ 0 := by
  unfold hb
  rw [hermitian_form_rank_zero_apply, if_pos (by simp)]
  have := wb_last_ne hz
  have e : yb z (Fin.last (2 * 0 + k)) = z ⟨r + k, by omega⟩ := by
    unfold yb; congr 1; ext; rw [eB_lr]; simp
  rw [e]; simpa using this

def lastRow (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (2 * 0 + k) → Fin r → ℂ) (a : Fin r) : ℂ :=
  -(∑ i, c i a * conj (hb z i.castSucc)) / conj (hb z (Fin.last (2 * 0 + k)))

def extC (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (2 * 0 + k) → Fin r → ℂ) : Fin (2 * 0 + k + 1) → Fin r → ℂ :=
  fun v a => Fin.lastCases (lastRow z c a) (fun i => c i a) v

lemma extC_add (z : Fin (2 * r + k + 1) → ℂ) (c c' : Fin (2 * 0 + k) → Fin r → ℂ) :
    extC z (c + c') = extC z c + extC z c' := by
  funext v a
  refine Fin.lastCases ?_ (fun i => ?_) v
  · simp only [extC, Fin.lastCases_last, Pi.add_apply, lastRow]
    rw [← add_div]; congr 1
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add]
  · simp [extC]

def Cstr (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (2 * 0 + k + 1) → Fin r → ℂ) : Prop :=
  (Matrix.of c)ᴴ *ᵥ hb z = 0

lemma cstr_iff {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (c : Fin (2 * 0 + k + 1) → Fin r → ℂ) :
    Cstr z c ↔ c = extC z (fun i a => c i.castSucc a) := by
  have hl := hb_last_ne hz
  have hl' : conj (hb z (Fin.last (2 * 0 + k))) ≠ 0 := by simpa using hl
  have hsum : ∀ a, ((Matrix.of c)ᴴ *ᵥ hb z) a =
      (∑ i : Fin (2 * 0 + k), conj (c i.castSucc a) * hb z i.castSucc) +
        conj (c (Fin.last _) a) * hb z (Fin.last _) := by
    intro a
    simp only [Matrix.mulVec, dotProduct, conjTranspose_apply, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc]; rfl
  constructor
  · intro h
    funext v a
    have ha := congrFun h a
    rw [hsum] at ha
    refine Fin.lastCases ?_ (fun i => ?_) v
    · simp only [extC, Fin.lastCases_last, lastRow]
      rw [eq_div_iff hl']
      have := congrArg conj ha
      simp only [Pi.zero_apply, map_add, map_sum, map_mul, Complex.conj_conj, map_zero] at this
      linear_combination this
    · simp [extC]
  · intro h
    funext a
    rw [hsum]
    have hl2 : c (Fin.last _) a = lastRow z (fun i a => c i.castSucc a) a := by
      conv_lhs => rw [h]
      simp [extC]
    rw [hl2]
    simp only [lastRow, map_div₀, map_neg, map_sum, map_mul, Complex.conj_conj, Pi.zero_apply]
    field_simp
    ring

lemma cstr_extC {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (c : Fin (2 * 0 + k) → Fin r → ℂ) :
    Cstr z (extC z c) := by
  rw [cstr_iff hz]
  funext v a
  refine Fin.lastCases ?_ (fun i => ?_) v <;> simp [extC]

end coords

section param

variable {k r : ℕ}

abbrev X0 (k r : ℕ) : Type := (Fin (2 * 0 + k) → Fin r → ℂ) × ((G.UT r → ℂ) × (Fin r → ℝ))

def embX (z : Fin (2 * r + k + 1) → ℂ) (x : X0 k r) : RC k r 0 := (extC z x.1, x.2)

def E (z : Fin (2 * r + k + 1) → ℂ) (x : X0 k r) : B.Mat k r := Rn k r 0 (embX z x)

def mulX (z : Fin (2 * r + k + 1) → ℂ) (x1 x2 : X0 k r) : X0 k r :=
  (x1.1 + x2.1, x1.2 + x2.2 + kap (Matrix.of (extC z x1.1)) (Matrix.of (extC z x2.1)))

theorem E_mul (z : Fin (2 * r + k + 1) → ℂ) (x1 x2 : X0 k r) : E z x1 * E z x2 = E z (mulX z x1 x2) := by
  unfold E; rw [rn_mul]; congr 1
  simp only [mulC, embX, mulX, extC_add]

lemma w_mulVec_inj {d : ℕ} {v : Fin d → ℂ} (h : G.wMat d *ᵥ v = 0) : v = 0 := by
  have := congrArg (G.wMat d *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, wMat_sq, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact this

theorem rn_fix_z_iff {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (x : RC k r 0) :
    Rn k r 0 x *ᵥ z = z ↔ Cstr z x.1 := by
  obtain ⟨h1, h2, h3⟩ := rn_mulVec x hz.1
  have ha : a12 x *ᵥ yb z = -(G.wMat r *ᵥ ((Matrix.of x.1)ᴴ *ᵥ hb z)) := by
    simp only [a12, hb, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  constructor
  · intro h
    have h0 : a12 x *ᵥ yb z = 0 := by
      funext a
      have := h1 a
      rw [h, wb_ll hz.1] at this
      exact this.symm
    rw [ha, neg_eq_zero] at h0
    exact w_mulVec_inj h0
  · intro h
    unfold Cstr at h
    have h0 : a12 x *ᵥ yb z = 0 := by rw [ha, h, Matrix.mulVec_zero, neg_zero]
    funext i
    obtain ⟨p, rfl⟩ := (eB k r 0).surjective i
    rcases p with (a | v) | a
    · rw [h1, h0, wb_ll hz.1]; rfl
    · rw [h2]; rfl
    · rw [h3, wb_r hz.1]

lemma stabilizer_fixes_flag_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r}
    (hn : n ∈ C2.N0set k r z) (b : Fin (r + 1)) : n *ᵥ fvec k r z b = fvec k r z b := by
  have hS : n ∈ Sset k r z := ⟨1, Formalism.FourierDecayAlt.P.Dx2.Rad.one_UW z, n, hn.1, (Matrix.one_mul n).symm⟩
  rw [((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz).1 n hS).1 b, hn.2]
  simp [Matrix.one_apply]

theorem E_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (x : X0 k r) : E z x ∈ C2.N0set k r z := by
  have hN : E z x ∈ Nset k r := rset_sub_nset (rn_rset (embX z x))
  refine ⟨hN, Formalism.FourierDecayAlt.P.Dx2.VV.uMap_fix hz fun b => ?_⟩
  unfold fvec
  split_ifs with hb
  · exact rn_col _ ⟨b.val, hb⟩
  · exact (rn_fix_z_iff hz _).2 (cstr_extC hz x.1)

theorem stabilizer_subset_range {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r}
    (hn : n ∈ C2.N0set k r z) : ∃ x, E z x = n := by
  have hR : n ∈ Rset k r 0 := by
    refine ⟨hn.1.1, fun i b hb => ?_, fun i b hb1 hb2 hi => hn.1.2.2 i b hb1 (by omega) hi⟩
    have hf := stabilizer_fixes_flag_vector hz hn ⟨b.val, by omega⟩
    unfold fvec at hf
    rw [dif_pos hb] at hf
    have := congrFun hf i
    have e : eI k r ⟨b.val, hb⟩ = b := Fin.ext rfl
    rw [e] at this
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, Matrix.one_apply, eq_comm] using this
  obtain ⟨x, rfl⟩ := rset_sub_range hR
  have hz' : Rn k r 0 x *ᵥ z = z := by
    have := stabilizer_fixes_flag_vector hz hn (Fin.last r)
    unfold fvec at this; rw [dif_neg (by simp)] at this; exact this
  have hc := (cstr_iff hz x.1).1 ((rn_fix_z_iff hz x).1 hz')
  refine ⟨(fun i a => x.1 i.castSucc a, x.2), ?_⟩
  unfold E embX
  congr 1
  exact Prod.ext hc.symm rfl

end param

section haar

variable {k r : ℕ}

theorem cont_uMap (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun x : Mt k r => C2.uMap k r z (Matrix.of x) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun x : Mt k r => C2.uMap k r z (Matrix.of x) a b
  unfold C2.uMap
  split_ifs with h
  · exact (B2x5.continuous_herm _).comp ((Continuous.matrix_mulVec continuous_id continuous_const).prodMk continuous_const)
  · exact ((B2x5.continuous_herm _).comp ((Continuous.matrix_mulVec continuous_id continuous_const).prodMk
      continuous_const)).div_const _

theorem isClosed_setOf_of_mem_n0set (z : Fin (2 * r + k + 1) → ℂ) : IsClosed {x : Mt k r | Matrix.of x ∈ C2.N0set k r z} := by
  have h1 : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed
  have h2 : IsClosed {x : Mt k r | C2.uMap k r z (Matrix.of x) = 1} := isClosed_eq (cont_uMap z) continuous_const
  exact h1.inter h2

theorem cont_extC (z : Fin (2 * r + k + 1) → ℂ) : Continuous (extC (k := k) (r := r) z) := by
  refine continuous_pi fun v => continuous_pi fun a => ?_
  refine Fin.lastCases ?_ (fun i => ?_) v
  · simp only [extC, Fin.lastCases_last, lastRow]
    refine (Continuous.neg ?_).div_const _
    exact continuous_finset_sum _ fun i _ => (continuous_apply_apply i a).mul continuous_const
  · simp only [extC, Fin.lastCases_castSucc]
    exact continuous_apply_apply i a

theorem cont_ofExtC (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun c : Fin (2 * 0 + k) → Fin r → ℂ => (Matrix.of (extC z c) : Matrix (Fin (2 * 0 + k + 1)) (Fin r) ℂ) :=
  cont_extC z

theorem cont_skc {j : ℕ} : Continuous fun M : Matrix (Fin j) (Fin j) ℂ => skc M := by
  unfold skc
  refine Continuous.prodMk (continuous_pi fun p => ?_) (continuous_pi fun a => ?_)
  · exact continuous_apply_apply p.1.1 p.1.2
  · exact Complex.continuous_im.comp (continuous_apply_apply a a)

theorem cont_kap {X : Type*} [TopologicalSpace X] {f g : X → Matrix (Fin (2 * 0 + k + 1)) (Fin r) ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => kap (f x) (g x) := by
  unfold kap
  exact cont_skc.comp ((((hg.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hf).sub
    ((hf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hg)).const_smul (1 / 2 : ℂ))

instance instHaarQ : (volume : Measure ((G.UT r → ℂ) × (Fin r → ℝ))).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

instance instHaarC : (volume : Measure (Fin (2 * 0 + k) → Fin r → ℂ)).IsAddHaarMeasure :=
  Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite

instance instIsAddHaarCoordinates : (volume : Measure (X0 k r)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

def Et (z : Fin (2 * r + k + 1) → ℂ) (x : X0 k r) : Mt k r := Matrix.of.symm (E z x)

theorem cont_Et (z : Fin (2 * r + k + 1) → ℂ) : Continuous (Et (k := k) (r := r) z) := by
  have h := Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) r 0
  have he : Continuous fun x : X0 k r => embX z x := (cont_extC z).comp continuous_fst |>.prodMk continuous_snd
  exact h.comp he

theorem mp_mulX_left (z : Fin (2 * r + k + 1) → ℂ) (x0 : X0 k r) :
    MeasurePreserving (mulX z x0) volume volume := by
  have hk : Continuous fun c : Fin (2 * 0 + k) → Fin r → ℂ =>
      kap (Matrix.of (extC z x0.1)) (Matrix.of (extC z c)) := cont_kap continuous_const (cont_ofExtC z)
  have := MeasurePreserving.skew_product (μa := (volume : Measure (Fin (2 * 0 + k) → Fin r → ℂ)))
    (μc := (volume : Measure ((G.UT r → ℂ) × (Fin r → ℝ))))
    (μd := (volume : Measure ((G.UT r → ℂ) × (Fin r → ℝ))))
    (measurePreserving_add_left volume x0.1)
    (g := fun c q => (x0.2 + kap (Matrix.of (extC z x0.1)) (Matrix.of (extC z c))) + q)
    (((continuous_const.add (hk.comp continuous_fst)).add continuous_snd).measurable)
    (Filter.Eventually.of_forall fun c => map_add_left_eq_self volume _)
  have e : mulX z x0 = fun p : X0 k r =>
      (x0.1 + p.1, (x0.2 + kap (Matrix.of (extC z x0.1)) (Matrix.of (extC z p.1))) + p.2) := by
    funext x; simp only [mulX]; refine Prod.ext rfl ?_; show x0.2 + x.2 + _ = (x0.2 + _) + x.2; abel
  rw [e, Measure.volume_eq_prod]; exact this

theorem mp_mulX_right (z : Fin (2 * r + k + 1) → ℂ) (x0 : X0 k r) :
    MeasurePreserving (fun x => mulX z x x0) volume volume := by
  have hk : Continuous fun c : Fin (2 * 0 + k) → Fin r → ℂ =>
      kap (Matrix.of (extC z c)) (Matrix.of (extC z x0.1)) := cont_kap (cont_ofExtC z) continuous_const
  have := MeasurePreserving.skew_product (μa := (volume : Measure (Fin (2 * 0 + k) → Fin r → ℂ)))
    (μc := (volume : Measure ((G.UT r → ℂ) × (Fin r → ℝ))))
    (μd := (volume : Measure ((G.UT r → ℂ) × (Fin r → ℝ))))
    (measurePreserving_add_left volume x0.1)
    (g := fun c q => (x0.2 + kap (Matrix.of (extC z c)) (Matrix.of (extC z x0.1))) + q)
    (((continuous_const.add (hk.comp continuous_fst)).add continuous_snd).measurable)
    (Filter.Eventually.of_forall fun c => map_add_left_eq_self volume _)
  have e : (fun x => mulX z x x0) = fun p : X0 k r =>
      (x0.1 + p.1, (x0.2 + kap (Matrix.of (extC z p.1)) (Matrix.of (extC z x0.1))) + p.2) := by
    funext x; simp only [mulX]; refine Prod.ext (add_comm _ _) ?_
    show x.2 + x0.2 + _ = (x0.2 + _) + x.2; abel
  rw [e, Measure.volume_eq_prod]; exact this

def cOf (M : Mt k r) : Matrix (Fin (2 * 0 + k + 1)) (Fin r) ℂ :=
  Matrix.of fun v a => M (eB k r 0 (Sum.inl (Sum.inr v))) (eB k r 0 (Sum.inr a))

def sOf (M : Mt k r) : Matrix (Fin r) (Fin r) ℂ :=
  G.wMat r * (Matrix.of fun a b => M (eB k r 0 (Sum.inl (Sum.inl a))) (eB k r 0 (Sum.inr b))) +
    (1 / 2 : ℂ) • ((cOf M)ᴴ * Hpk k 0 * cOf M)

def Rd (M : Mt k r) : X0 k r := (fun i a => cOf M i.castSucc a, skc (sOf M))

theorem cont_Rd : Continuous (Rd (k := k) (r := r)) := by
  have hc : Continuous (cOf (k := k) (r := r)) :=
    continuous_pi fun v => continuous_pi fun a => by simp only [cOf, Matrix.of_apply]; exact continuous_apply_apply _ _
  have h13 : Continuous fun M : Mt k r =>
      (Matrix.of fun a b => M (eB k r 0 (Sum.inl (Sum.inl a))) (eB k r 0 (Sum.inr b)) : Matrix (Fin r) (Fin r) ℂ) :=
    continuous_pi fun a => continuous_pi fun b => by simp only [Matrix.of_apply]; exact continuous_apply_apply _ _
  refine Continuous.prodMk (continuous_pi fun i => continuous_pi fun a => ?_) (cont_skc.comp ?_)
  · exact (continuous_apply a).comp ((continuous_apply i.castSucc).comp hc)
  · exact (continuous_const.matrix_mul h13).add
      (((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc).const_smul (1 / 2 : ℂ))

lemma skc_skewOf {j : ℕ} (q : (G.UT j → ℂ) × (Fin j → ℝ)) : skc (skewOf q) = q := by
  refine Prod.ext (funext fun p => ?_) (funext fun a => ?_)
  · exact skewOf_lt q p.2
  · show (skewOf q a a).im = q.2 a
    rw [skewOf_diag]; simp

theorem Rd_Et (z : Fin (2 * r + k + 1) → ℂ) (x : X0 k r) : Rd (Et z x) = x := by
  have hc : cOf (Et z x) = Matrix.of (extC z x.1) := by
    ext v a; simp [cOf, Et, E, embX, Ux3.rn_eq, block3_apply]
  have hs : sOf (Et z x) = skewOf x.2 := by
    have h13 : (Matrix.of fun a b => (Et z x) (eB k r 0 (Sum.inl (Sum.inl a))) (eB k r 0 (Sum.inr b)) :
        Matrix (Fin r) (Fin r) ℂ) = G.wMat r * ((-(1 / 2 : ℂ)) • ((Matrix.of (extC z x.1))ᴴ * Hpk k 0 *
          Matrix.of (extC z x.1)) + skewOf x.2) := by
      ext a b; simp [Et, E, embX, Ux3.rn_eq, block3_apply]
    unfold sOf; rw [h13, hc, wMat_sq_assoc]
    module
  unfold Rd; rw [hs, skc_skewOf]
  refine Prod.ext ?_ rfl
  funext i a; rw [hc]; simp [extC]

def mu0 (z : Fin (2 * r + k + 1) → ℂ) : Measure (Mt k r) := (volume : Measure (X0 k r)).map (Et z)

theorem Et_mul (z : Fin (2 * r + k + 1) → ℂ) (x1 x2 : X0 k r) :
    Matrix.of (Et z x1) * Matrix.of (Et z x2) = Matrix.of (Et z (mulX z x1 x2)) := E_mul z x1 x2

theorem isHaar_stabilizer_measure {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : B.IsHaarOn (C2.N0set k r z) (mu0 z) := by
  have hm : Measurable (Et (k := k) (r := r) z) := (cont_Et z).measurable
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show mu0 z ({x : Mt k r | Matrix.of x ∈ C2.N0set k r z}ᶜ) = 0
    unfold mu0
    rw [Measure.map_apply hm (isClosed_setOf_of_mem_n0set z).measurableSet.compl]
    have : Et z ⁻¹' {x : Mt k r | Matrix.of x ∈ C2.N0set k r z}ᶜ = ∅ := by
      ext x; simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact E_mem hz x
    rw [this, measure_empty]
  · intro a ha
    obtain ⟨x0, rfl⟩ := stabilizer_subset_range hz ha
    unfold mu0
    rw [Measure.map_map (Formalism.FourierDecayAlt.P.Dx2.OrbJ.contL _).measurable hm]
    have e : lmulM (E z x0) ∘ Et z = Et z ∘ mulX z x0 := by
      funext x; exact E_mul z x0 x
    rw [e, ← Measure.map_map hm (mp_mulX_left z x0).measurable, (mp_mulX_left z x0).map_eq]
  · intro a ha
    obtain ⟨x0, rfl⟩ := stabilizer_subset_range hz ha
    unfold mu0
    have hr : Continuous (B.rmulF (E z x0)) := by
      unfold B.rmulF; exact (continuous_id.matrix_mul continuous_const)
    rw [Measure.map_map hr.measurable hm]
    have e : B.rmulF (E z x0) ∘ Et z = Et z ∘ fun x => mulX z x x0 := by
      funext x; exact E_mul z x x0
    rw [e, ← Measure.map_map hm (mp_mulX_right z x0).measurable, (mp_mulX_right z x0).map_eq]
  · intro K hK
    unfold mu0
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    have hsub : Et z ⁻¹' K ⊆ Rd '' K := fun x hx => ⟨Et z x, hx, Rd_Et z x⟩
    exact (measure_mono hsub).trans_lt ((hK.image cont_Rd).measure_lt_top)
  · unfold mu0
    refine (Measure.map_ne_zero_iff hm.aemeasurable).mpr ?_
    intro h0
    have := (Measure.IsOpenPosMeasure.open_pos (μ := (volume : Measure (X0 k r))) Set.univ isOpen_univ Set.univ_nonempty)
    rw [h0] at this; exact this rfl

end haar

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

section disint

variable {k r : ℕ}

lemma det_UT {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]

lemma upper_mem {m : ℕ} (u : G.UT m → ℂ) : G.upper u ∈ C2.UTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [G.upper, G.strictUpper, Matrix.one_apply, ne_of_gt hij, not_lt.mpr hij.le]
  · simp [G.upper, G.strictUpper]

lemma utc_upper {m : ℕ} (u : G.UT m → ℂ) : StabilizerDisintegration.utc (G.upper u) = u := by
  funext q
  simp [StabilizerDisintegration.utc, G.upper, G.strictUpper, q.2, ne_of_lt q.2, Matrix.one_apply]

lemma upper_utc {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M ∈ C2.UTset m) : G.upper (StabilizerDisintegration.utc M) = M := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [G.upper, G.strictUpper, StabilizerDisintegration.utc, h, ne_of_lt h, Matrix.one_apply]
  · simp [G.upper, G.strictUpper, hM.2]
  · simp [G.upper, G.strictUpper, h, ne_of_gt h, not_lt.mpr h.le, Matrix.one_apply, hM.1 i j h]

lemma UT_mul {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) (hB : B ∈ C2.UTset m) :
    A * B ∈ C2.UTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA.1 i l h, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2, hB.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hB.1 l i h, mul_zero]
    · simp

lemma inv_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, hH]

def mXa (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) : B.Mat k r := fun i j =>
  if hi : i.val < r then (if hj : j.val < r then vX ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
  else if hi' : r + k < i.val then
    (if hj' : r + k < j.val then (vXᴴ).adjugate ⟨2 * r + k - i.val, by omega⟩ ⟨2 * r + k - j.val, by omega⟩ else 0)
  else if i = j then 1 else 0

lemma mX_eq {vX : Matrix (Fin r) (Fin r) ℂ} (h : vX.det = 1) : C2.mX k r vX = mXa k r vX := by
  have hi : (vXᴴ)⁻¹ = (vXᴴ).adjugate := by
    rw [Matrix.inv_def, Matrix.det_conjTranspose, h]; simp
  funext i j
  simp only [C2.mX, mXa, hi]

lemma cont_mXa : Continuous (mXa k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun vX : Matrix (Fin r) (Fin r) ℂ => mXa k r vX i j
  unfold mXa
  split_ifs
  · exact continuous_apply_apply _ _
  · exact continuous_const
  · exact (continuous_apply_apply _ _).comp (continuous_id.matrix_conjTranspose.matrix_adjugate)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

lemma cont_xiV : Continuous (C2.xiV k r) := by
  refine continuous_pi fun i => ?_
  unfold C2.xiV
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma cont_nEich (z : Fin (2 * r + k + 1) → ℂ) : Continuous (C2.nEich k r z) := by
  unfold C2.nEich
  have hx := cont_xiV (k := k) (r := r)
  refine continuous_const.add (Continuous.const_smul (((hx.matrix_vecMulVec continuous_const).neg.add
    (continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec hx).star)).add
    ((hx.matrix_vecMulVec (continuous_const.matrix_mulVec hx).star).const_smul (1 / 2 : ℂ)))
    ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)))

lemma sub_upper_mem (u : G.UT (r + 1) → ℂ) :
    (G.upper u).submatrix Fin.castSucc Fin.castSucc ∈ C2.UTset r := by
  have h := upper_mem u
  refine ⟨fun i j hij => h.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij), fun i => h.2 _⟩

theorem cont_tauU (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun u : G.UT (r + 1) → ℂ => C2.tauM k r z (G.upper u) := by
  have hup : Continuous (G.upper (d := r + 1)) := Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper
  have e : (fun u : G.UT (r + 1) → ℂ => C2.tauM k r z (G.upper u)) = fun u =>
      C2.nEich k r z (fun a => G.upper u a.castSucc (Fin.last r)) *
        mXa k r ((G.upper u).submatrix Fin.castSucc Fin.castSucc) := by
    funext u
    unfold C2.tauM
    rw [mX_eq (det_UT (sub_upper_mem u))]
  rw [e]
  refine ((cont_nEich z).comp ?_).matrix_mul (cont_mXa.comp ?_)
  · exact continuous_pi fun a => (continuous_apply_apply _ _).comp hup
  · exact hup.matrix_submatrix _ _

end disint

section disint2

variable {k r : ℕ}

lemma N_sub_S {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.Dx2.Rad.one_UW z, n, hn, (Matrix.one_mul n).symm⟩

lemma uMap_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s t : B.Mat k r} (hs : s ∈ Nset k r)
    (ht : t ∈ Nset k r) : C2.uMap k r z (s * t) = C2.uMap k r z s * C2.uMap k r z t :=
  ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz).1 s (N_sub_S hs)).2.2 t (N_sub_S ht)

lemma uMap_UT {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r} (hs : s ∈ Nset k r) :
    C2.uMap k r z s ∈ C2.UTset (r + 1) :=
  ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz).1 s (N_sub_S hs)).2.1

lemma uMap_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    C2.uMap k r z n⁻¹ = (C2.uMap k r z n)⁻¹ := by
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have h1 : C2.uMap k r z n⁻¹ * C2.uMap k r z n = 1 := by
    rw [← uMap_mul hz (hN.inv_mem n hn) hn, Matrix.nonsing_inv_mul _ (hN.unit n hn)]
    exact Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one z hz
  exact (Matrix.inv_eq_left_inv h1).symm

lemma tau_N {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hv : v ∈ C2.UTset (r + 1)) : C2.tauM k r z v ∈ Nset k r := (Formalism.FourierDecayAlt.P.c2_tau_mem k r z hz v hv).1

lemma tau_u {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hv : v ∈ C2.UTset (r + 1)) : C2.uMap k r z (C2.tauM k r z v) = v :=
  (Formalism.FourierDecayAlt.P.c2_tau_mem k r z hz v hv).2.2

lemma mul_upper_sub {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) (x : G.UT m → ℂ) (q : G.UT m) :
    (A * G.upper x) q.1.1 q.1.2 - x q =
      ∑ l, if q.1.1 < l then A q.1.1 l * G.upper x l q.1.2 else 0 := by
  obtain ⟨⟨i, j⟩, hij⟩ := q
  simp only
  have hterm : ∀ l, A i l * G.upper x l j =
      (if i < l then A i l * G.upper x l j else 0) + (if l = i then G.upper x i j else 0) := by
    intro l
    rcases lt_trichotomy l i with h | rfl | h
    · rw [hA.1 i l h, zero_mul, if_neg (not_lt.mpr h.le), if_neg (ne_of_lt h), add_zero]
    · rw [hA.2, one_mul, if_neg (lt_irrefl _), if_pos rfl, zero_add]
    · rw [if_pos h, if_neg (ne_of_gt h), add_zero]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have hx : G.upper x i j = x ⟨(i, j), hij⟩ := by
    simp [G.upper, G.strictUpper, hij, ne_of_lt hij, Matrix.one_apply]
  rw [hx]; ring

theorem mp_UTleft {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) :
    MeasurePreserving (fun u : G.UT m → ℂ => StabilizerDisintegration.utc (A * G.upper u)) volume volume := by
  refine Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp (fun q : G.UT m => q.1.2.val - q.1.1.val) _ ?_ ?_
  · refine measurable_pi_lambda _ fun q => ?_
    exact ((continuous_const.matrix_mul Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper).matrix_elem q.1.1 q.1.2).measurable
  · intro q x y hxy
    show (A * G.upper x) q.1.1 q.1.2 - x q = (A * G.upper y) q.1.1 q.1.2 - y q
    rw [mul_upper_sub hA, mul_upper_sub hA]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · congr 1
      simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
      split_ifs with hlj
      · rw [hxy ⟨(l, q.1.2), hlj⟩ (by have := q.2; simp only; omega)]
      · rfl
    · rfl

def Phi (z : Fin (2 * r + k + 1) → ℂ) (p : (G.UT (r + 1) → ℂ) × Mt k r) : Mt k r :=
  Matrix.of.symm (C2.tauM k r z (G.upper p.1) * Matrix.of p.2)

lemma cont_Phi (z : Fin (2 * r + k + 1) → ℂ) : Continuous (Phi (k := k) (r := r) z) :=
  ((cont_tauU z).comp continuous_fst).matrix_mul continuous_snd

lemma cont_utc {m : ℕ} : Continuous (StabilizerDisintegration.utc (m := m)) :=
  continuous_pi fun q => continuous_apply_apply _ _

def bC (z : Fin (2 * r + k + 1) → ℂ) (a : B.Mat k r) (u : G.UT (r + 1) → ℂ) : B.Mat k r :=
  Hpk k r * (C2.tauM k r z (C2.uMap k r z a * G.upper u))ᴴ * Hpk k r * a * C2.tauM k r z (G.upper u)

lemma cont_bC (z : Fin (2 * r + k + 1) → ℂ) (a : B.Mat k r) (ha : a ∈ Nset k r)
    (hz : C2.StdZ k r z) : Continuous (bC (k := k) (r := r) z a) := by
  have hA := uMap_UT hz ha
  have e : (fun u : G.UT (r + 1) → ℂ => C2.tauM k r z (C2.uMap k r z a * G.upper u)) =
      (fun u => C2.tauM k r z (G.upper u)) ∘ fun u => StabilizerDisintegration.utc (C2.uMap k r z a * G.upper u) := by
    funext u; simp only [Function.comp, upper_utc (UT_mul hA (upper_mem u))]
  have h1 : Continuous fun u : G.UT (r + 1) → ℂ => C2.tauM k r z (C2.uMap k r z a * G.upper u) := by
    rw [e]; exact (cont_tauU z).comp (cont_utc.comp (continuous_const.matrix_mul Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper))
  unfold bC
  exact (((continuous_const.matrix_mul h1.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_mul (cont_tauU z)

lemma bC_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {a : B.Mat k r} (ha : a ∈ Nset k r)
    (u : G.UT (r + 1) → ℂ) :
    bC z a u = (C2.tauM k r z (C2.uMap k r z a * G.upper u))⁻¹ * a * C2.tauM k r z (G.upper u) := by
  have hT := tau_N hz (UT_mul (uMap_UT hz ha) (upper_mem u))
  rw [inv_GV hT.1]; rfl

lemma bC_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {a : B.Mat k r} (ha : a ∈ Nset k r)
    (u : G.UT (r + 1) → ℂ) : bC z a u ∈ C2.N0set k r z := by
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hA := uMap_UT hz ha
  have hAU := UT_mul hA (upper_mem u)
  have hT1 := tau_N hz hAU
  have hT0 := tau_N hz (upper_mem u)
  rw [bC_eq hz ha]
  have hmem1 : (C2.tauM k r z (C2.uMap k r z a * G.upper u))⁻¹ * a ∈ Nset k r := hN.mul_mem _ (hN.inv_mem _ hT1) _ ha
  refine ⟨hN.mul_mem _ hmem1 _ hT0, ?_⟩
  rw [uMap_mul hz hmem1 hT0, uMap_mul hz (hN.inv_mem _ hT1) ha, uMap_inv hz hT1, tau_u hz hAU, tau_u hz (upper_mem u)]
  have hdet : IsUnit (C2.uMap k r z a * G.upper u).det := by rw [det_UT hAU]; exact isUnit_one
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

lemma Phi_S {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {a : B.Mat k r} (ha : a ∈ Nset k r)
    (p : (G.UT (r + 1) → ℂ) × Mt k r) :
    Phi z (StabilizerDisintegration.utc (C2.uMap k r z a * G.upper p.1), lmulM (bC z a p.1) p.2) = lmulM a (Phi z p) := by
  have hAU := UT_mul (uMap_UT hz ha) (upper_mem p.1)
  have hT1 := tau_N hz hAU
  unfold Phi lmulM
  rw [upper_utc hAU, bC_eq hz ha]
  simp only [Matrix.of_symm_apply, Matrix.of_apply]
  show C2.tauM k r z (C2.uMap k r z a * G.upper p.1) * ((C2.tauM k r z (C2.uMap k r z a * G.upper p.1))⁻¹ * a *
      C2.tauM k r z (G.upper p.1) * Matrix.of p.2) = a * (C2.tauM k r z (G.upper p.1) * Matrix.of p.2)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).unit _ hT1), Matrix.one_mul, Matrix.mul_assoc]

theorem disint {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {μ0 μN : Measure (Mt k r)}
    (h0 : B.IsHaarOn (C2.N0set k r z) μ0) (hN : B.IsHaarOn (Nset k r) μN) :
    ∃ c : NNReal, 0 < c ∧ μN = c • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map (Phi z) := by
  have hNc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  haveI := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF h0
  haveI := Formalism.FourierDecayAlt.P.Dx2.OrbJ.fmoc h0
  have hPm : Measurable (Phi (k := k) (r := r) z) := (cont_Phi z).measurable
  set P := ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map (Phi z) with hP
  have hNcl : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := hNc.closed
  have hN0cl : IsClosed {x : Mt k r | Matrix.of x ∈ C2.N0set k r z} := isClosed_setOf_of_mem_n0set z
  have h0c : μ0 {x : Mt k r | Matrix.of x ∈ C2.N0set k r z}ᶜ = 0 := h0.conc
  have hbad : ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0)
      (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∈ C2.N0set k r z}ᶜ) = 0 := by
    rw [Measure.prod_prod, h0c, mul_zero]

  have hconc : P {x : Mt k r | Matrix.of x ∈ Nset k r}ᶜ = 0 := by
    rw [hP, Measure.map_apply hPm hNcl.measurableSet.compl]
    refine measure_mono_null (fun p hp => ?_) hbad
    refine ⟨Set.mem_univ _, fun h2 => hp ?_⟩
    exact hNc.mul_mem _ (tau_N hz (upper_mem p.1)) _ h2.1

  have hleft : ∀ a ∈ Nset k r, P.map (lmulM a) = P := by
    intro a ha
    have hA := uMap_UT hz ha
    have hS : MeasurePreserving (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        (StabilizerDisintegration.utc (C2.uMap k r z a * G.upper p.1), lmulM (bC z a p.1) p.2))
        ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0) ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0) := by
      refine MeasurePreserving.skew_product (mp_UTleft hA) (g := fun u n => lmulM (bC z a u) n) ?_
        (Filter.Eventually.of_forall fun u => h0.left _ (bC_mem hz ha u))
      have hcb : Continuous fun p : (G.UT (r + 1) → ℂ) × Mt k r => (lmulM (bC z a p.1) p.2 : Mt k r) :=
        ((cont_bC z a ha hz).comp continuous_fst).matrix_mul continuous_snd
      exact hcb.measurable
    rw [hP, Measure.map_map (Formalism.FourierDecayAlt.P.Dx2.OrbJ.contL a).measurable hPm]
    have e : lmulM a ∘ Phi z = Phi z ∘ fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        (StabilizerDisintegration.utc (C2.uMap k r z a * G.upper p.1), lmulM (bC z a p.1) p.2) := by
      funext p; exact (Phi_S hz ha p).symm
    rw [e, ← Measure.map_map hPm hS.measurable, hS.map_eq]

  have hfin : ∀ K : Set (Mt k r), IsCompact K → P K < ⊤ := by
    intro K hK
    rw [hP, Measure.map_apply hPm hK.isClosed.measurableSet]
    set f1 : Mt k r → G.UT (r + 1) → ℂ := fun x => StabilizerDisintegration.utc (C2.uMap k r z (Matrix.of x))
    set f2 : Mt k r → Mt k r := fun x =>
      Matrix.of.symm (Hpk k r * (C2.tauM k r z (G.upper (f1 x)))ᴴ * Hpk k r * Matrix.of x)
    have hf1 : Continuous f1 := cont_utc.comp (cont_uMap z)
    have hf2 : Continuous f2 :=
      ((continuous_const.matrix_mul ((cont_tauU z).comp hf1).matrix_conjTranspose).matrix_mul
        continuous_const).matrix_mul continuous_id
    have hsub : Phi z ⁻¹' K ⊆ ((f1 '' K) ×ˢ (f2 '' K)) ∪ (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∈ C2.N0set k r z}ᶜ) := by
      intro p hp
      by_cases h2 : Matrix.of p.2 ∈ C2.N0set k r z
      · left
        have hT := tau_N hz (upper_mem p.1)
        have hu : C2.uMap k r z (Matrix.of (Phi z p)) = G.upper p.1 := by
          show C2.uMap k r z (C2.tauM k r z (G.upper p.1) * Matrix.of p.2) = G.upper p.1
          rw [uMap_mul hz hT h2.1, tau_u hz (upper_mem p.1), h2.2, Matrix.mul_one]
        have e1 : f1 (Phi z p) = p.1 := by simp only [f1, hu, utc_upper]
        refine ⟨⟨Phi z p, hp, e1⟩, ⟨Phi z p, hp, ?_⟩⟩
        simp only [f2, e1]
        rw [← inv_GV hT.1]
        show (C2.tauM k r z (G.upper p.1))⁻¹ * (C2.tauM k r z (G.upper p.1) * Matrix.of p.2) = Matrix.of p.2
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hNc.unit _ hT), Matrix.one_mul]
      · right; exact ⟨Set.mem_univ _, h2⟩
    refine (measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt ?_)
    rw [hbad, add_zero, Measure.prod_prod]
    exact ENNReal.mul_lt_top ((hK.image hf1).measure_lt_top) ((hK.image hf2).measure_lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Nset k r) μN P hNc hN hconc hleft hfin
  have hP0 : P ≠ 0 := by
    rw [hP]
    refine (Measure.map_ne_zero_iff hPm.aemeasurable).mpr ?_
    intro h
    have := congrArg (fun μ : Measure ((G.UT (r + 1) → ℂ) × Mt k r) => μ Set.univ) h
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [← Set.univ_prod_univ, Measure.prod_prod] at this
    have hv : (volume : Measure (G.UT (r + 1) → ℂ)) Set.univ ≠ 0 :=
      (Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty)
    have hm : μ0 Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr h0.ne_zero
    exact mul_ne_zero hv hm this
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact hP0 hc
  refine ⟨c⁻¹, inv_pos.mpr (pos_iff_ne_zero.mpr hc0), ?_⟩
  rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end disint2

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration

theorem exists_haar_stabilizer : ExistsHaarStabilizer := fun k r z hz => ⟨HC.mu0 z, HC.isHaar_stabilizer_measure hz⟩

theorem disintN : DisintN := fun k r z hz μ0 μN h0 hN => HC.disint hz h0 hN

end Formalism.FourierDecayAlt.P.StabilizerDisintegration
