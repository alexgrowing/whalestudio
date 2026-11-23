import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_TypeNormMeas_TC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.TF

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vec

variable {k r : ℕ}

def InW (k r : ℕ) (z x : Fin (2 * r + k + 1) → ℂ) : Prop := inWb k r x ∧ herm (Hpk k r) x z = 0

theorem herm_swap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w v = star (herm (Hpk k r) v w) :=
  (P.Qx2.herm_star v w).symm

theorem herm_alt {z : Fin (2 * r + k + 1) → ℂ} : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
  have h := P.Qx2.herm_star (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem herm_zz_ne {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [herm_alt]
  exact_mod_cast (neg_ne_zero.2 hT.ne')

theorem herm_wbP {y w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    herm (Hpk k r) y w = herm (Hpk k r) (SSn.wbP k r y) w := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hw i hi, star_zero, zero_mul, zero_mul]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold SSn.wbP Hpk
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [if_pos hj]
    · rw [if_neg hj]
      have h1 : ¬ (i.val < r ∧ i.val + j.val = 2 * r + k) := by omega
      have h2 : ¬ (j.val < r ∧ i.val + j.val = 2 * r + k) := by omega
      have h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
        rintro ⟨-, -, rfl⟩; omega
      simp [h1, h2, h3]

theorem blockProjection_add (x y : Fin (2 * r + k + 1) → ℂ) : SSn.wbP k r (x + y) = SSn.wbP k r x + SSn.wbP k r y := by
  funext i; simp only [SSn.wbP, Pi.add_apply]; split_ifs <;> simp

theorem blockProjection_smul (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) : SSn.wbP k r (c • x) = c • SSn.wbP k r x := by
  funext i; simp only [SSn.wbP, Pi.smul_apply]; split_ifs <;> simp

theorem blockProjection_mem_block (x : Fin (2 * r + k + 1) → ℂ) : inWb k r (SSn.wbP k r x) := by
  intro i hi; unfold SSn.wbP; rw [if_neg (by omega)]

theorem prWv_add (z x y : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (x + y) = SSn.prWv k r z x + SSn.prWv k r z y := by
  unfold SSn.prWv
  rw [blockProjection_add, P.Qx8.herm_add_left', add_div, add_smul]
  abel

theorem prWv_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (c • x) = c • SSn.prWv k r z x := by
  unfold SSn.prWv
  rw [blockProjection_smul, P.Qx8.herm_smul_left', smul_add, smul_smul, mul_div_assoc]

theorem inWb_add {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y) : inWb k r (x + y) := by
  intro i hi; simp [hx i hi, hy i hi]

theorem inWb_smul (c : ℂ) {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : inWb k r (c • x) := by
  intro i hi; simp [hx i hi]

theorem prWv_inW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (y : Fin (2 * r + k + 1) → ℂ) :
    InW k r z (SSn.prWv k r z y) := by
  refine ⟨inWb_add (blockProjection_mem_block y) (inWb_smul _ hz), ?_⟩
  unfold SSn.prWv
  rw [P.Qx8.herm_add_left', P.Qx8.herm_smul_left', herm_alt]
  have : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp
  push_cast
  ring

theorem herm_z_w {z w : Fin (2 * r + k + 1) → ℂ} (hw : InW k r z w) : herm (Hpk k r) z w = 0 := by
  rw [herm_swap, hw.2, star_zero]

theorem herm_prWv {z y w : Fin (2 * r + k + 1) → ℂ} (hw : InW k r z w) :
    herm (Hpk k r) y w = herm (Hpk k r) (SSn.prWv k r z y) w := by
  unfold SSn.prWv
  rw [P.Qx8.herm_add_left', P.Qx8.herm_smul_left', herm_z_w hw, mul_zero, add_zero, herm_wbP hw.1]

theorem eq_sum_herm_smul_frame_of_inW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {F : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : InW k r z v) : v = ∑ p, herm (Hpk k r) v (F p) • F p := by
  conv_lhs => rw [P.SkewHermitianParts.complete hz (herm_zz_ne hT) hF hv.1]
  rw [hv.2, zero_mul, zero_smul, add_zero]

theorem frame_inW {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {F : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hF : Q.IsFrameOf k r [z] F) (p : Fin m) : InW k r z (F p) :=
  ⟨hF.1 p, hF.2.2 p z (by simp)⟩

theorem proj_frame {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {F : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (y : Fin (2 * r + k + 1) → ℂ) :
    ∑ p, herm (Hpk k r) y (F p) • F p = SSn.prWv k r z y := by
  conv_rhs => rw [eq_sum_herm_smul_frame_of_inW hz hT hF (prWv_inW hz hT y)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← herm_prWv (frame_inW hF p)]

theorem frame_uw {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) {m : ℕ}
    {F : Fin m → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) : Q.IsFrameOf k r [z] (fun p => h *ᵥ F p) := by
  refine ⟨fun p => P.CutBP.TNM.tc_inWb hh (hF.1 p), fun p q => ?_, fun p v hv => ?_⟩
  · rw [P.Qx2.herm_uh hh.1]; exact hF.2.1 p q
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    rw [← hh.2.2, P.Qx2.herm_uh hh.1]
    exact hF.2.2 p _ (by simp)

theorem prWv_uw {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (y : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (h *ᵥ y) = h *ᵥ SSn.prWv k r z y := by
  obtain ⟨F, hF⟩ := P.Qx8.frame_exists hz hT
  rw [← proj_frame hz hT (frame_uw hh hF), ← proj_frame hz hT hF, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [P.Qx2.herm_uh hh.1, Matrix.mulVec_smul]

end vec

section mat

variable {k r : ℕ}

theorem ebM_eq_unitB (v b : Fin (2 * r + k + 1) → ℂ) : ebM k r v b = Q.unitB (Hpk k r) ![v, b] 0 1 := by
  unfold ebM Q.unitB; simp

theorem ebM_mulVec (v b x : Fin (2 * r + k + 1) → ℂ) : ebM k r v b *ᵥ x = herm (Hpk k r) x b • v := by
  rw [ebM_eq_unitB, P.Qx8.unitB_mulVec]; simp

theorem ebM_frame {m : ℕ} (F : Fin m → Fin (2 * r + k + 1) → ℂ) (p s : Fin m) :
    ebM k r (F p) (F s) = Q.unitB (Hpk k r) F p s := rfl

theorem ebM_add_left (v v' b : Fin (2 * r + k + 1) → ℂ) : ebM k r (v + v') b = ebM k r v b + ebM k r v' b := by
  apply P.Qx8.mat_ext; intro x; simp only [Matrix.add_mulVec, ebM_mulVec, smul_add]

theorem ebM_smul_left (c : ℂ) (v b : Fin (2 * r + k + 1) → ℂ) : ebM k r (c • v) b = c • ebM k r v b := by
  apply P.Qx8.mat_ext; intro x; simp only [Matrix.smul_mulVec, ebM_mulVec, smul_comm c]

theorem ebM_add_right (v b b' : Fin (2 * r + k + 1) → ℂ) : ebM k r v (b + b') = ebM k r v b + ebM k r v b' := by
  apply P.Qx8.mat_ext; intro x; simp only [Matrix.add_mulVec, ebM_mulVec, P.Qx8.herm_add_right', add_smul]

theorem ebM_smul_right (c : ℂ) (v b : Fin (2 * r + k + 1) → ℂ) : ebM k r v (c • b) = star c • ebM k r v b := by
  apply P.Qx8.mat_ext; intro x; simp only [Matrix.smul_mulVec, ebM_mulVec, P.Qx8.herm_smul_right', smul_smul]

theorem ebM_zero_left (b : Fin (2 * r + k + 1) → ℂ) : ebM k r 0 b = 0 := by
  apply P.Qx8.mat_ext; intro x; simp [ebM_mulVec]

theorem ebM_zero_right (v : Fin (2 * r + k + 1) → ℂ) : ebM k r v 0 = 0 := by
  apply P.Qx8.mat_ext; intro x; simp [ebM_mulVec, herm]

theorem ebM_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (b : Fin (2 * r + k + 1) → ℂ) : ebM k r (∑ i ∈ s, c i • v i) b = ∑ i ∈ s, c i • ebM k r (v i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ebM_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ebM_add_left, ebM_smul_left, ih]

theorem ebM_sum_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (b : ι → Fin (2 * r + k + 1) → ℂ) : ebM k r v (∑ i ∈ s, c i • b i) = ∑ i ∈ s, star (c i) • ebM k r v (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ebM_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ebM_add_right, ebM_smul_right, ih]

theorem ebM_conj {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v b : Fin (2 * r + k + 1) → ℂ) :
    h * ebM k r v b * h⁻¹ = ebM k r (h *ᵥ v) (h *ᵥ b) := by
  apply P.Qx8.mat_ext; intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ebM_mulVec, ebM_mulVec, Matrix.mulVec_smul]
  congr 1
  rw [← P.Qx2.herm_uh hh, P.Qx8.inv_mulVec_uh hh]

def GW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Z : B.Mat k r) : Prop :=
  P.QrD.InLieW k r z (hpart1 (Hpk k r) Z) ∧ P.QrD.InLieW k r z (hpart2 (Hpk k r) Z)

theorem GW_ebM {z v b : Fin (2 * r + k + 1) → ℂ} (hv : InW k r z v) (hb : InW k r z b) : GW k r z (ebM k r v b) := by
  rw [ebM_eq_unitB]
  have hB : ∀ a, inWb k r (![v, b] a) := by
    intro a; fin_cases a
    · exact hv.1
    · exact hb.1
  have hl := P.Qx8.unitB_lie ![v, b] hB (Fin.last r) 0 1
  have z1 : Q.unitB (Hpk k r) ![v, b] 0 1 *ᵥ z = 0 := by
    rw [P.Qx8.unitB_mulVec]; simp [herm_z_w hb]
  have z2 : Q.unitB (Hpk k r) ![v, b] 1 0 *ᵥ z = 0 := by
    rw [P.Qx8.unitB_mulVec]; simp [herm_z_w hv]
  refine ⟨⟨hl.1, ?_⟩, ⟨hl.2, ?_⟩⟩
  · rw [P.Qx8.hpart1_unitB, Matrix.smul_mulVec, Matrix.sub_mulVec, z1, z2]; simp
  · rw [P.Qx8.hpart2_unitB, Matrix.smul_mulVec, Matrix.add_mulVec, z1, z2]; simp

theorem hpart1_add (Z Z' : B.Mat k r) :
    hpart1 (Hpk k r) (Z + Z') = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) Z' := by
  unfold hpart1; rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]; congr 1; abel

theorem hpart2_add (Z Z' : B.Mat k r) :
    hpart2 (Hpk k r) (Z + Z') = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
  unfold hpart2; rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]; congr 1; abel

theorem inv_two_I : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
  field_simp; simp [Complex.I_sq]

theorem hermitian_adjoint_smul (c : ℂ) (Z : B.Mat k r) :
    (Hpk k r)⁻¹ * (c • Z)ᴴ * Hpk k r = star c • ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) := by
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem star_re_im (c : ℂ) : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
  rw [Complex.star_def]; apply Complex.ext <;> simp

theorem hpart1_smul (c : ℂ) (Z : B.Mat k r) :
    hpart1 (Hpk k r) (c • Z) = (c.re : ℂ) • hpart1 (Hpk k r) Z + ((-c.im : ℝ) : ℂ) • hpart2 (Hpk k r) Z := by
  unfold hpart1 hpart2
  rw [hermitian_adjoint_smul, inv_two_I, star_re_im]
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  push_cast
  linear_combination (Z i j / 2) * hc

theorem hpart2_smul (c : ℂ) (Z : B.Mat k r) :
    hpart2 (Hpk k r) (c • Z) = (c.re : ℂ) • hpart2 (Hpk k r) Z + (c.im : ℂ) • hpart1 (Hpk k r) Z := by
  unfold hpart1 hpart2
  rw [hermitian_adjoint_smul, inv_two_I, star_re_im]
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (-Complex.I / 2 * Z i j) * hc +
    ((c.im : ℂ) / 2 * (((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j - Z i j)) * Complex.I_sq

theorem GW_add {z : Fin (2 * r + k + 1) → ℂ} {Z Z' : B.Mat k r} (h : GW k r z Z) (h' : GW k r z Z') :
    GW k r z (Z + Z') := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_add]; exact P.LieBracketMultiplication.lie_add h.1 h'.1
  · rw [hpart2_add]; exact P.LieBracketMultiplication.lie_add h.2 h'.2

theorem GW_smul {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {Z : B.Mat k r} (h : GW k r z Z) : GW k r z (c • Z) := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_smul]; exact P.LieBracketMultiplication.lie_add (P.LieBracketMultiplication.lie_smul h.1 _) (P.LieBracketMultiplication.lie_smul h.2 _)
  · rw [hpart2_smul]; exact P.LieBracketMultiplication.lie_add (P.LieBracketMultiplication.lie_smul h.2 _) (P.LieBracketMultiplication.lie_smul h.1 _)

end mat

section ec

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : B.Mat k r → (W →L[ℂ] W)}

theorem ecOp_add (hR : Qr.IsRepW k r z π) {Z Z' : B.Mat k r} (h : GW k r z Z) (h' : GW k r z Z') :
    P.QrD.ecOp π (Z + Z') = P.QrD.ecOp π Z + P.QrD.ecOp π Z' := by
  unfold P.QrD.ecOp
  rw [hpart1_add, hpart2_add, (P.differential_operator_linear W k r z π hR _ _ h.1 h'.1).1,
    (P.differential_operator_linear W k r z π hR _ _ h.2 h'.2).1, smul_add]
  abel

theorem I_I_smul (x : W →L[ℂ] W) : Complex.I • Complex.I • x = -x := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem ecOp_smul (hR : Qr.IsRepW k r z π) (c : ℂ) {Z : B.Mat k r} (h : GW k r z Z) :
    P.QrD.ecOp π (c • Z) = c • P.QrD.ecOp π Z := by
  unfold P.QrD.ecOp
  rw [hpart1_smul, hpart2_smul,
    (P.differential_operator_linear W k r z π hR _ _ (P.LieBracketMultiplication.lie_smul h.1 _) (P.LieBracketMultiplication.lie_smul h.2 _)).1,
    (P.differential_operator_linear W k r z π hR _ _ (P.LieBracketMultiplication.lie_smul h.2 _) (P.LieBracketMultiplication.lie_smul h.1 _)).1,
    (P.differential_operator_linear W k r z π hR _ _ h.1 h.1).2, (P.differential_operator_linear W k r z π hR _ _ h.2 h.2).2,
    (P.differential_operator_linear W k r z π hR _ _ h.2 h.2).2, (P.differential_operator_linear W k r z π hR _ _ h.1 h.1).2]
  simp only [← Complex.coe_smul]
  conv_rhs => rw [(Complex.re_add_im c).symm]
  simp only [add_smul, smul_add, mul_smul, I_I_smul]
  push_cast
  module

theorem GW_zero : GW k r z 0 := by
  refine ⟨?_, ?_⟩
  · unfold hpart1; simpa using P.LieBracketMultiplication.lie_zero (k := k) (r := r) (z := z)
  · unfold hpart2; simpa using P.LieBracketMultiplication.lie_zero (k := k) (r := r) (z := z)

theorem ecOp_zero : P.QrD.ecOp π (0 : B.Mat k r) = 0 := by
  unfold P.QrD.ecOp hpart1 hpart2
  simp [P.SkewHermitianParts.dOp_zero]

theorem ecOp_sum (hR : Qr.IsRepW k r z π) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Z : ι → B.Mat k r)
    (hZ : ∀ i, GW k r z (Z i)) : P.QrD.ecOp π (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • P.QrD.ecOp π (Z i) := by
  classical
  have hG : ∀ t : Finset ι, GW k r z (∑ i ∈ t, c i • Z i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (GW_zero (k := k) (r := r) (z := z))
    | insert a t ha ih => rw [Finset.sum_insert ha]; exact GW_add (GW_smul _ (hZ a)) ih
  induction s using Finset.induction_on with
  | empty => simp [ecOp_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ecOp_add hR (GW_smul _ (hZ a)) (hG s), ecOp_smul hR _ (hZ a), ih]

theorem hermitian_adjoint_conj_unitary {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (Z : B.Mat k r) :
    (Hpk k r)⁻¹ * (h * Z * h⁻¹)ᴴ * Hpk k r = h * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * h⁻¹ := by
  have hg : hᴴ * Hpk k r * h = Hpk k r := hh
  have e : ∀ M : B.Mat k r, Hpk k r * (Hpk k r * M) = M := by
    intro M; rw [← Matrix.mul_assoc, P.Qx2.hpk_sq', Matrix.one_mul]
  have hinv : h⁻¹ = Hpk k r * hᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hg, P.Qx2.hpk_sq']
  rw [hinv, P.Qx2.hpk_inv]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, P.Qx2.hpk_h, Matrix.mul_assoc, e]

theorem hpart1_conj {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (Z : B.Mat k r) :
    hpart1 (Hpk k r) (h * Z * h⁻¹) = h * hpart1 (Hpk k r) Z * h⁻¹ := by
  unfold hpart1; rw [hermitian_adjoint_conj_unitary hh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem hpart2_conj {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (Z : B.Mat k r) :
    hpart2 (Hpk k r) (h * Z * h⁻¹) = h * hpart2 (Hpk k r) Z * h⁻¹ := by
  unfold hpart2; rw [hermitian_adjoint_conj_unitary hh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

theorem ecOp_conj (hR : Qr.IsRepW k r z π) {h : B.Mat k r} (hh : h ∈ UWset k r z) {Z : B.Mat k r}
    (hZ : GW k r z Z) :
    P.QrD.ecOp π (h * Z * h⁻¹) = (π h).comp ((P.QrD.ecOp π Z).comp (π h⁻¹)) := by
  unfold P.QrD.ecOp
  rw [hpart1_conj hh.1, hpart2_conj hh.1, (P.differential_operator_adjoint W k r z π hR _ hZ.1 h hh).2.2,
    (P.differential_operator_adjoint W k r z π hR _ hZ.2 h hh).2.2]
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp]

end ec

section gen

variable {k r : ℕ}

theorem herm_sum_right {ι : Type*} (s : Finset ι) (x : Fin (2 * r + k + 1) → ℂ) (c : ι → ℂ)
    (w : ι → Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (∑ i ∈ s, c i • w i) = ∑ i ∈ s, star (c i) * herm (Hpk k r) x (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.Qx8.herm_add_right', P.Qx8.herm_smul_right', ih]

theorem herm_sum_left {ι : Type*} (s : Finset ι) (x : Fin (2 * r + k + 1) → ℂ) (c : ι → ℂ)
    (w : ι → Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ i ∈ s, c i • w i) x = ∑ i ∈ s, c i * herm (Hpk k r) (w i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.Qx8.herm_add_left', P.Qx8.herm_smul_left', ih]

theorem prWv_sum (z : Fin (2 * r + k + 1) → ℂ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (v : ι → Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • SSn.prWv k r z (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := prWv_smul z 0 (0 : Fin (2 * r + k + 1) → ℂ)
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, prWv_add, prWv_smul, ih]

theorem frame_gram {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {F G : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hG : Q.IsFrameOf k r [z] G) (t u : Fin k) :
    ∑ q, herm (Hpk k r) (F q) (G t) * star (herm (Hpk k r) (F q) (G u)) = if u = t then 1 else 0 := by
  have e : ∑ q, herm (Hpk k r) (F q) (G t) * star (herm (Hpk k r) (F q) (G u)) =
      herm (Hpk k r) (G u) (∑ q, herm (Hpk k r) (G t) (F q) • F q) := by
    rw [herm_sum_right]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [herm_swap (F q) (G t), herm_swap (F q) (G u), star_star, mul_comm]
  rw [e, ← eq_sum_herm_smul_frame_of_inW hz hT hF (frame_inW hG t)]
  exact hG.2.1 u t

theorem frame_trace {M : Type*} [AddCommGroup M] [Module ℂ M] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hT : 0 < Tz k r z) (S : (Fin (2 * r + k + 1) → ℂ) → (Fin (2 * r + k + 1) → ℂ) → M)
    (hL : ∀ (c : Fin k → ℂ) (v : Fin k → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      (∀ i, InW k r z (v i)) → InW k r z w → S (∑ i, c i • v i) w = ∑ i, c i • S (v i) w)
    (hR : ∀ (c : Fin k → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (w : Fin k → Fin (2 * r + k + 1) → ℂ),
      InW k r z v → (∀ i, InW k r z (w i)) → S v (∑ i, c i • w i) = ∑ i, star (c i) • S v (w i))
    {F G : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hG : Q.IsFrameOf k r [z] G) :
    ∑ q, S (F q) (F q) = ∑ t, S (G t) (G t) := by
  have hexp : ∀ q, F q = ∑ t, herm (Hpk k r) (F q) (G t) • G t := fun q => eq_sum_herm_smul_frame_of_inW hz hT hG (frame_inW hF q)
  have hGw : ∀ t, InW k r z (G t) := frame_inW hG
  have hsum : ∀ (c : Fin k → ℂ), InW k r z (∑ t, c t • G t) := by
    intro c
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun t _ => by simp [(hGw t).1 i hi]
    · rw [herm_sum_left]; exact Finset.sum_eq_zero fun t _ => by rw [(hGw t).2, mul_zero]
  calc ∑ q, S (F q) (F q)
      = ∑ q, ∑ t, ∑ u, (herm (Hpk k r) (F q) (G t) * star (herm (Hpk k r) (F q) (G u))) • S (G t) (G u) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        conv_lhs => rw [hexp q]
        rw [hL _ _ _ hGw (hsum _)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hR _ _ _ (hGw t) hGw, Finset.smul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [smul_smul]
    _ = ∑ t, ∑ u, (∑ q, herm (Hpk k r) (F q) (G t) * star (herm (Hpk k r) (F q) (G u))) • S (G t) (G u) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ t, S (G t) (G t) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        simp_rw [frame_gram hz hT hF hG t]
        simp

end gen

section smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cd_lin (f : E → ℂ) (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : ℝ) x, f (c • x) = (c : ℂ) * f x) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  let L : E →ₗ[ℝ] ℂ :=
    { toFun := f, map_add' := hadd, map_smul' := fun c x => by rw [hsmul, RingHom.id_apply, Complex.real_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem cd_herm {k r : ℕ} (g : E → Fin (2 * r + k + 1) → ℂ) (hadd : ∀ x y, g (x + y) = g x + g y)
    (hsmul : ∀ (c : ℝ) x, g (c • x) = (c : ℂ) • g x) (v : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => herm (Hpk k r) (g x) v) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (herm (Hpk k r) (g x) v)) := by
  refine ⟨cd_lin _ (fun x y => by rw [hadd, P.Qx8.herm_add_left']) (fun c x => by rw [hsmul, P.Qx8.herm_smul_left']),
    cd_lin _ (fun x y => by rw [hadd, P.Qx8.herm_add_left', star_add])
      (fun c x => by rw [hsmul, P.Qx8.herm_smul_left', star_mul', Complex.star_def, Complex.conj_ofReal])⟩

end smooth

section sandwA

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem sandw_apply (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) :
    sandw A B' X = A.comp (X.comp B') := rfl

end sandwA

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem trace_move (U V : Wq →L[ℂ] Wp) (B₁ B₂ : Wq →L[ℂ] Wq) (hB : ∀ u v, inner ℂ (B₁ u) v = inner ℂ u (B₂ v)) :
    ∑ i, inner ℂ (U (stdOrthonormalBasis ℂ Wq i)) (V (B₁ (stdOrthonormalBasis ℂ Wq i))) =
      ∑ i, inner ℂ (U (B₂ (stdOrthonormalBasis ℂ Wq i))) (V (stdOrthonormalBasis ℂ Wq i)) := by
  set b := stdOrthonormalBasis ℂ Wq
  have hexp : ∀ x, x = ∑ j, inner ℂ (b j) x • b j := fun x => (b.sum_repr' x).symm
  calc ∑ i, inner ℂ (U (b i)) (V (B₁ (b i)))
      = ∑ i, ∑ j, inner ℂ (b j) (B₁ (b i)) * inner ℂ (U (b i)) (V (b j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [hexp (B₁ (b i))]
        simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    _ = ∑ j, ∑ i, inner ℂ (b j) (B₁ (b i)) * inner ℂ (U (b i)) (V (b j)) := Finset.sum_comm
    _ = ∑ j, inner ℂ (U (B₂ (b j))) (V (b j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_rhs => rw [hexp (B₂ (b j))]
        simp only [map_sum, map_smul, sum_inner, inner_smul_left]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        rw [← inner_conj_symm, hB, inner_conj_symm]

theorem hs_sandw_adj (A₁ A₂ : Wp →L[ℂ] Wp) (B₁ B₂ : Wq →L[ℂ] Wq) (hA : ∀ u v, inner ℂ (A₂ u) v = inner ℂ u (A₁ v))
    (hB : ∀ u v, inner ℂ (B₁ u) v = inner ℂ u (B₂ v)) (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (sandw A₁ B₁ X) Y = B.hsInner X (sandw A₂ B₂ Y) := by
  rw [P.Topx1.hsInner_eq, P.Topx1.hsInner_eq]
  simp only [sandw_apply, ContinuousLinearMap.comp_apply]
  simp only [← hA]
  exact trace_move (A₂.comp Y) X B₁ B₂ hB

theorem hs_sum_left {ι : Type*} (s : Finset ι) (T : ι → Wq →L[ℂ] Wp) (Y : Wq →L[ℂ] Wp) :
    B.hsInner (∑ i ∈ s, T i) Y = ∑ i ∈ s, B.hsInner (T i) Y := by
  simp only [P.Topx1.hsInner_eq, ContinuousLinearMap.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem hs_sum_right {ι : Type*} (s : Finset ι) (X : Wq →L[ℂ] Wp) (T : ι → Wq →L[ℂ] Wp) :
    B.hsInner X (∑ i ∈ s, T i) = ∑ i ∈ s, B.hsInner X (T i) := by
  simp only [P.Topx1.hsInner_eq, ContinuousLinearMap.sum_apply, sum_inner]
  exact Finset.sum_comm

theorem hs_smul_left (c : ℂ) (T Y : Wq →L[ℂ] Wp) : B.hsInner (c • T) Y = c * B.hsInner T Y := by
  simp only [P.Topx1.hsInner_eq, ContinuousLinearMap.smul_apply, inner_smul_right, Finset.mul_sum]

theorem hs_smul_right (c : ℂ) (X T : Wq →L[ℂ] Wp) : B.hsInner X (c • T) = star c * B.hsInner X T := by
  simp only [P.Topx1.hsInner_eq, ContinuousLinearMap.smul_apply, inner_smul_left, Finset.mul_sum, Complex.star_def]

end hs

section main

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem sandw_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (A : ι → Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) :
    sandw (∑ i ∈ s, c i • A i) B' = ∑ i ∈ s, c i • sandw (A i) B' := by
  classical
  induction s using Finset.induction_on with
  | empty => ext X x; simp [sandw_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    ext X x; simp [sandw_apply]

theorem sandw_sum_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (A : Wp →L[ℂ] Wp) (B' : ι → Wq →L[ℂ] Wq) :
    sandw A (∑ i ∈ s, c i • B' i) = ∑ i ∈ s, c i • sandw A (B' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext X x; simp [sandw_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    ext X x; simp [sandw_apply]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
  {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}

theorem tht_form (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (a a' : Fin (2 * r + k + 1) → ℂ)
    (ι : B.Mat k r) :
    tht k r z z' π π' F F' a a' ι = ∑ q, sandw (P.QrD.ecOp π (ebM k r (SSn.prWv k r z (ι *ᵥ F' q)) (SSn.prWv k r z a)))
      (P.QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') (F' q))) := by
  unfold tht
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← sandw_sum_left, ← ecOp_sum hR _ _ _ (fun p => GW_ebM (frame_inW hF p) (prWv_inW hz hT a)),
    ← ebM_sum_left, proj_frame hz hT hF]

theorem thtA_form (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (a a' : Fin (2 * r + k + 1) → ℂ)
    (ι : B.Mat k r) :
    thtA k r z z' π π' F F' a a' ι = ∑ q, sandw (P.QrD.ecOp π (ebM k r (SSn.prWv k r z a) (SSn.prWv k r z (ι *ᵥ F' q))))
      (P.QrD.ecOp π' (ebM k r (F' q) (SSn.prWv k r z' a'))) := by
  unfold thtA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have e := ecOp_sum hR Finset.univ (fun p => star (herm (Hpk k r) (ι *ᵥ F' q) (F p)))
    (fun p => ebM k r (SSn.prWv k r z a) (F p)) (fun p => GW_ebM (prWv_inW hz hT a) (frame_inW hF p))
  rw [← ebM_sum_right] at e
  simp only [Complex.star_def] at e
  rw [← sandw_sum_left, ← e, proj_frame hz hT hF]

theorem tht_indep (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F G F' G' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hG : Q.IsFrameOf k r [z] G)
    (hF' : Q.IsFrameOf k r [z'] F') (hG' : Q.IsFrameOf k r [z'] G') (a a' : Fin (2 * r + k + 1) → ℂ)
    (ι : B.Mat k r) : tht k r z z' π π' F F' a a' ι = tht k r z z' π π' G G' a a' ι := by
  rw [tht_form hz hT hR hF, tht_form hz hT hR hG]
  refine frame_trace hz' hT' (fun v w => sandw (P.QrD.ecOp π (ebM k r (SSn.prWv k r z (ι *ᵥ v)) (SSn.prWv k r z a)))
      (P.QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') w))) ?_ ?_ hF' hG'
  · intro c v w hv hw
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, prWv_sum, ebM_sum_left]
    rw [ecOp_sum hR _ _ _ (fun i => GW_ebM (prWv_inW hz hT _) (prWv_inW hz hT a)), sandw_sum_left]
  · intro c v w hv hw
    simp only [ebM_sum_right]
    rw [ecOp_sum hR' _ _ _ (fun i => GW_ebM (prWv_inW hz' hT' a') (hw i)), sandw_sum_right]

theorem thtA_indep (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F G F' G' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hG : Q.IsFrameOf k r [z] G)
    (hF' : Q.IsFrameOf k r [z'] F') (hG' : Q.IsFrameOf k r [z'] G') (a a' : Fin (2 * r + k + 1) → ℂ)
    (ι : B.Mat k r) : thtA k r z z' π π' F F' a a' ι = thtA k r z z' π π' G G' a a' ι := by
  rw [thtA_form hz hT hR hF, thtA_form hz hT hR hG]
  refine frame_trace hz' hT' (fun v w => sandw (P.QrD.ecOp π (ebM k r (SSn.prWv k r z a) (SSn.prWv k r z (ι *ᵥ w))))
      (P.QrD.ecOp π' (ebM k r v (SSn.prWv k r z' a')))) ?_ ?_ hF' hG'
  · intro c v w hv hw
    simp only [ebM_sum_left]
    rw [ecOp_sum hR' _ _ _ (fun i => GW_ebM (hv i) (prWv_inW hz' hT' a')), sandw_sum_right]
  · intro c v w hv hw
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, prWv_sum, ebM_sum_right]
    rw [ecOp_sum hR _ _ _ (fun i => GW_ebM (prWv_inW hz hT a) (prWv_inW hz hT _)), sandw_sum_left]

omit [FiniteDimensional ℂ Wp] in
theorem rep_inv_cancel {zz : Fin (2 * r + k + 1) → ℂ} {ρ : B.Mat k r → (Wp →L[ℂ] Wp)} (hR : Qr.IsRepW k r zz ρ)
    {h : B.Mat k r} (hh : h ∈ UWset k r zz) (v : Wp) : ρ h⁻¹ (ρ h v) = v := by
  have e := hR.1.2 _ (P.LieBracketMultiplication.uw_inv hh) _ hh
  rw [Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), hR.1.1] at e
  have := congrArg (fun L : Wp →L[ℂ] Wp => L v) e
  simpa using this.symm

theorem mulVec_conj_cancel {h h' ι : B.Mat k r} (hh' : h' ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    (h * ι * h'⁻¹) *ᵥ (h' *ᵥ v) = h *ᵥ (ι *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh'), Matrix.mul_one,
    Matrix.mulVec_mulVec]

theorem sandw_conj (hR : Qr.IsRepW k r z π) (hR' : Qr.IsRepW k r z' π') {h h' : B.Mat k r} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z') (E : Wp →L[ℂ] Wp) (E' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) :
    sandw ((π h).comp (E.comp (π h⁻¹))) ((π' h').comp (E'.comp (π' h'⁻¹))) ((π h).comp (X.comp (π' h'⁻¹))) =
      (π h).comp ((sandw E E' X).comp (π' h'⁻¹)) := by
  ext x
  simp only [sandw_apply, ContinuousLinearMap.comp_apply, rep_inv_cancel hR hh, rep_inv_cancel hR' hh']

theorem tht_eqv (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    {h h' : B.Mat k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (a a' : Fin (2 * r + k + 1) → ℂ)
    (ι : B.Mat k r) (X : Wq →L[ℂ] Wp) :
    tht k r z z' π π' F F' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹) ((π h).comp (X.comp (π' h'⁻¹))) =
      (π h).comp ((tht k r z z' π π' F F' a a' ι X).comp (π' h'⁻¹)) := by
  rw [tht_indep hz hT hR hz' hT' hR' hF (frame_uw hh hF) hF' (frame_uw hh' hF')]
  conv_rhs => rw [← sandw_apply (π h) (π' h'⁻¹)]
  unfold tht
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
  congr 1
  · rw [mulVec_conj_cancel hh'.1, P.Qx2.herm_uh hh.1]
  rw [prWv_uw hz hT hh, prWv_uw hz' hT' hh', ← ebM_conj hh.1,
    ← ebM_conj hh'.1, ecOp_conj hR hh (GW_ebM (frame_inW hF p) (prWv_inW hz hT a)),
    ecOp_conj hR' hh' (GW_ebM (prWv_inW hz' hT' a') (frame_inW hF' q)), sandw_conj hR hR' hh hh', sandw_apply]
  exact rfl

theorem thtA_eqv (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    {h h' : B.Mat k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (a a' : Fin (2 * r + k + 1) → ℂ)
    (ι : B.Mat k r) (X : Wq →L[ℂ] Wp) :
    thtA k r z z' π π' F F' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹) ((π h).comp (X.comp (π' h'⁻¹))) =
      (π h).comp ((thtA k r z z' π π' F F' a a' ι X).comp (π' h'⁻¹)) := by
  rw [thtA_indep hz hT hR hz' hT' hR' hF (frame_uw hh hF) hF' (frame_uw hh' hF')]
  conv_rhs => rw [← sandw_apply (π h) (π' h'⁻¹)]
  unfold thtA
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
  congr 1
  · rw [mulVec_conj_cancel hh'.1, P.Qx2.herm_uh hh.1]
  rw [prWv_uw hz hT hh, prWv_uw hz' hT' hh', ← ebM_conj hh.1,
    ← ebM_conj hh'.1, ecOp_conj hR hh (GW_ebM (prWv_inW hz hT a) (frame_inW hF p)),
    ecOp_conj hR' hh' (GW_ebM (frame_inW hF' q) (prWv_inW hz' hT' a')), sandw_conj hR hR' hh hh', sandw_apply]
  exact rfl

theorem sandw_smul_smul (c d : ℂ) (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) :
    sandw (c • A) (d • B') = (c * d) • sandw A B' := by
  ext X x; simp [sandw_apply, mul_smul, smul_comm c d]

theorem tht_phase (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    (c : ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    tht k r z z' π π' F F' (c • a) (conj c • a') ι = (conj c) ^ 2 • tht k r z z' π π' F F' a a' ι := by
  unfold tht
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [prWv_smul, prWv_smul, ebM_smul_right, ebM_smul_left,
    ecOp_smul hR _ (GW_ebM (frame_inW hF p) (prWv_inW hz hT a)),
    ecOp_smul hR' _ (GW_ebM (prWv_inW hz' hT' a') (frame_inW hF' q)), sandw_smul_smul, smul_smul, smul_smul,
    Complex.star_def]
  congr 1
  ring

theorem eA (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π) {F : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hF : Q.IsFrameOf k r [z] F) (p : Fin k) (a : Fin (2 * r + k + 1) → ℂ) :
    P.QrD.ecOp π (ebM k r (F p) (SSn.prWv k r z a)) =
      ∑ s, star (herm (Hpk k r) a (F s)) • P.QrD.ecOp π (Q.unitB (Hpk k r) F p s) := by
  conv_lhs => rw [eq_sum_herm_smul_frame_of_inW hz hT hF (prWv_inW hz hT a)]
  rw [ebM_sum_right, ecOp_sum hR _ _ _ (fun s => GW_ebM (frame_inW hF p) (frame_inW hF s))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← herm_prWv (frame_inW hF s)]
  rfl

theorem eA' (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π) {F : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hF : Q.IsFrameOf k r [z] F) (p : Fin k) (a : Fin (2 * r + k + 1) → ℂ) :
    P.QrD.ecOp π (ebM k r (SSn.prWv k r z a) (F p)) =
      ∑ s, herm (Hpk k r) a (F s) • P.QrD.ecOp π (Q.unitB (Hpk k r) F s p) := by
  conv_lhs => rw [eq_sum_herm_smul_frame_of_inW hz hT hF (prWv_inW hz hT a)]
  rw [ebM_sum_left, ecOp_sum hR _ _ _ (fun s => GW_ebM (frame_inW hF s) (frame_inW hF p))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← herm_prWv (frame_inW hF s)]
  rfl

theorem tht_expand (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    tht k r z z' π π' F F' a a' ι = ∑ p, ∑ q, ∑ s, ∑ t,
      (herm (Hpk k r) (ι *ᵥ F' q) (F p) * (star (herm (Hpk k r) a (F s)) * herm (Hpk k r) a' (F' t))) •
        sandw (P.QrD.ecOp π (Q.unitB (Hpk k r) F p s)) (P.QrD.ecOp π' (Q.unitB (Hpk k r) F' t q)) := by
  unfold tht
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [eA hz hT hR hF p a, eA' hz' hT' hR' hF' q a', sandw_sum_left]
  simp only [sandw_sum_right, Finset.smul_sum, smul_smul]

theorem thtA_expand (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    thtA k r z z' π π' F F' a a' ι = ∑ p, ∑ q, ∑ s, ∑ t,
      (star (herm (Hpk k r) (ι *ᵥ F' q) (F p)) * (herm (Hpk k r) a (F s) * star (herm (Hpk k r) a' (F' t)))) •
        sandw (P.QrD.ecOp π (Q.unitB (Hpk k r) F s p)) (P.QrD.ecOp π' (Q.unitB (Hpk k r) F' q t)) := by
  unfold thtA
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [eA' hz hT hR hF p a, eA hz' hT' hR' hF' q a', sandw_sum_left]
  simp only [sandw_sum_right, Finset.smul_sum, smul_smul, Complex.star_def]

theorem tht_smooth (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F') :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r =>
      tht k r z z' π π' F F' x.1 x.2.1 x.2.2) := by
  simp only [tht_expand hz hT hR hz' hT' hR' hF hF']
  have h1 : ∀ v w : Fin (2 * r + k + 1) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => herm (Hpk k r) (x.2.2 *ᵥ w) v) :=
    fun v w => (cd_herm (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => x.2.2 *ᵥ w)
      (fun x y => by simp [Matrix.add_mulVec]) (fun c x => by
        simp only [Prod.smul_snd, ← Complex.coe_smul, Matrix.smul_mulVec]) v).1
  have h2 : ∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => star (herm (Hpk k r) x.1 v)) :=
    fun v => (cd_herm (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => x.1)
      (fun x y => rfl) (fun c x => by simp only [Prod.smul_fst, ← Complex.coe_smul]) v).2
  have h3 : ∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => herm (Hpk k r) x.2.1 v) :=
    fun v => (cd_herm (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => x.2.1)
      (fun x y => rfl) (fun c x => by simp only [Prod.smul_snd, Prod.smul_fst, ← Complex.coe_smul]) v).1
  refine ContDiff.sum fun p _ => ContDiff.sum fun q _ => ContDiff.sum fun s _ => ContDiff.sum fun t _ => ?_
  exact ((h1 _ _).mul ((h2 _).mul (h3 _))).smul contDiff_const

theorem thtA_smooth (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F') :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r =>
      thtA k r z z' π π' F F' x.1 x.2.1 x.2.2) := by
  simp only [thtA_expand hz hT hR hz' hT' hR' hF hF']
  have h1 : ∀ v w : Fin (2 * r + k + 1) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => star (herm (Hpk k r) (x.2.2 *ᵥ w) v)) :=
    fun v w => (cd_herm (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => x.2.2 *ᵥ w)
      (fun x y => by simp [Matrix.add_mulVec]) (fun c x => by
        simp only [Prod.smul_snd, ← Complex.coe_smul, Matrix.smul_mulVec]) v).2
  have h2 : ∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => herm (Hpk k r) x.1 v) :=
    fun v => (cd_herm (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => x.1)
      (fun x y => rfl) (fun c x => by simp only [Prod.smul_fst, ← Complex.coe_smul]) v).1
  have h3 : ∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => star (herm (Hpk k r) x.2.1 v)) :=
    fun v => (cd_herm (fun x : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) × B.Mat k r => x.2.1)
      (fun x y => rfl) (fun c x => by simp only [Prod.smul_snd, Prod.smul_fst, ← Complex.coe_smul]) v).2
  refine ContDiff.sum fun p _ => ContDiff.sum fun q _ => ContDiff.sum fun s _ => ContDiff.sum fun t _ => ?_
  exact ((h1 _ _).mul ((h2 _).mul (h3 _))).smul contDiff_const

theorem tht_adj (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    (hu' : ∀ h ∈ UWset k r z', ∀ v, ‖π' h v‖ = ‖v‖)
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) (A B' : Wq →L[ℂ] Wp) :
    B.hsInner (tht k r z z' π π' F F' a a' ι A) B' = B.hsInner A (thtA k r z z' π π' F F' a a' ι B') := by
  rw [tht_expand hz hT hR hz' hT' hR' hF hF', thtA_expand hz hT hR hz' hT' hR' hF hF']
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hs_sum_left, hs_sum_right,
    hs_smul_left, hs_smul_right]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [hs_sandw_adj _ (P.QrD.ecOp π (Q.unitB (Hpk k r) F s p)) _ (P.QrD.ecOp π' (Q.unitB (Hpk k r) F' q t))
    (fun u v => P.Topx1.typ_EB_adj hR.1 hR.2 hu hF s p u v)
    (fun u v => P.Topx1.typ_EB_adj hR'.1 hR'.2 hu' hF' t q u v)]
  simp only [star_mul', star_star]

end main

theorem theta_facts_hold : ThtFacts := by
  intro Wp Wq _ _ _ _ _ _ P Bs hPl Bw Bw' hBw hBw'
  obtain ⟨hOK, hz, hz', hTe, hTe', hty, hty'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := hTe ▸ hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := hTe' ▸ hOK.T'_pos
  have hR : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨hty.2.1, hty.2.2.1⟩
  have hR' : Qr.IsRepW P.k P.r Bs.z' Bs.π' := ⟨hty'.2.1, hty'.2.2.1⟩
  refine ⟨tht_smooth hz hT hR hz' hT' hR' hBw hBw', thtA_smooth hz hT hR hz' hT' hR' hBw hBw',
    fun a a' ι A B' => tht_adj hz hT hR hty.2.2.2.1 hz' hT' hR' hty'.2.2.2.1 hBw hBw' a a' ι A B',
    fun h hh h' hh' a a' ι X => ⟨tht_eqv hz hT hR hz' hT' hR' hBw hBw' hh hh' a a' ι X,
      thtA_eqv hz hT hR hz' hT' hR' hBw hBw' hh hh' a a' ι X⟩,
    fun c a a' ι => tht_phase hz hT hR hz' hT' hR' hBw hBw' c a a' ι⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.TF

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem theta_facts_hold : ThtFacts := TF.theta_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
