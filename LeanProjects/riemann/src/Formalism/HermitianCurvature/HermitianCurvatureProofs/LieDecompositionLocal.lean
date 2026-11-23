import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_eq_fderiv {Φ Φ' : Mat k r → E} {U : Set (Mat k r)} {m : ℕ∞} (hm : 1 ≤ m) (hU : IsOpen U)
    {g X : Mat k r} (hgU : g ∈ U) (hgG : g ∈ GV k r) (hc : ContDiffOn ℝ (m : WithTop ℕ∞) Φ' U)
    (he : ∀ x ∈ U, x ∈ GV k r → Φ x = Φ' x) (hX : inLie k r X) :
    RdV X Φ g = fderiv ℝ Φ' g (g * X) := by
  have hd : DifferentiableAt ℝ Φ' g :=
    (hc.differentiableOn (by
      have : m ≠ 0 := by rintro rfl; simp at hm
      exact_mod_cast this)).differentiableAt (hU.mem_nhds hgU)
  exact (hasDerivAt_of_ext hU hgU hgG hX hd he).deriv

theorem inLie_comm {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X * Y - Y * X) := by
  unfold inLie at *
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_assoc Xᴴ, hX', hY', Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ,
    ← Matrix.mul_assoc Xᴴ, hY', hX']
  noncomm_ring

theorem rdV_comm {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) :
    RdV X (RdV Y Φ) g - RdV Y (RdV X Φ) g = RdV (X * Y - Y * X) Φ g := by
  obtain ⟨U, Φ', hU, hgU, hc, he⟩ := hloc
  have hc2 : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) Φ' U := by
    have : (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) := by norm_num
    rw [this]; exact hc
  have h1 := B4.op_op_ext false false hU hc2 he hX hY hgU hgG
  have h2 := B4.op_op_ext false false hU hc2 he hY hX hgU hgG
  simp only [B4.op_false, B4.vf_false] at h1 h2
  rw [h1, h2, rdV_eq_fderiv (m := 2) (by norm_num) hU hgU hgG hc he (inLie_comm hX hY)]
  have hsym : IsSymmSndFDerivAt ℝ Φ' g :=
    (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs := hsym (g * X) (g * Y)
  have e3 : (fderiv ℝ Φ' g) (g * (X * Y - Y * X)) =
      (fderiv ℝ Φ' g) (g * X * Y) - (fderiv ℝ Φ' g) (g * Y * X) := by
    rw [Matrix.mul_sub, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e3]
  have key : ∀ (a a' b c : E), a = a' → a + b - (a' + c) = b - c := by
    intro a a' b c h; rw [h]; abel
  exact key _ _ _ _ hs

theorem rdV_add {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) : RdV (X + Y) Φ g = RdV X Φ g + RdV Y Φ g := by
  obtain ⟨U, Φ', hU, hgU, hc, he⟩ := hloc
  rw [rdV_eq_fderiv le_rfl hU hgU hgG hc he hX, rdV_eq_fderiv le_rfl hU hgU hgG hc he hY,
    rdV_eq_fderiv le_rfl hU hgU hgG hc he (B4.inLie_add hX hY), Matrix.mul_add, map_add]

theorem rdV_rsmul {Φ : Mat k r → E} {g X : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (c : ℝ) : RdV ((c : ℂ) • X) Φ g = c • RdV X Φ g := by
  obtain ⟨U, Φ', hU, hgU, hc, he⟩ := hloc
  rw [rdV_eq_fderiv le_rfl hU hgU hgG hc he hX,
    rdV_eq_fderiv le_rfl hU hgU hgG hc he (B4.inLie_rsmul hX c)]
  have : g * ((c : ℂ) • X) = c • (g * X) := by
    rw [Matrix.mul_smul]; rfl
  rw [this, map_smul]

end Formalism.FourierDecayAlt.P.LieDecompositionLocal

namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def EZ (Z : Mat k r) (Φ : Mat k r → E) : Mat k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) Φ g + Complex.I • RdV (hpart2 (Hpk k r) Z) Φ g

theorem hermitian_part_mem_lie (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart1_lie Z
theorem antihermitian_part_mem_lie (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart2_lie Z

theorem hconj_lie {P : Mat k r} (hP : inLie k r P) : (Hpk k r)⁻¹ * Pᴴ * Hpk k r = -P := by
  unfold inLie at hP
  have hP' : Pᴴ * Hpk k r = -(Hpk k r * P) := eq_neg_of_add_eq_zero_left hP
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, Matrix.mul_assoc, hP', Matrix.mul_neg, ← Matrix.mul_assoc,
    Formalism.FourierDecayAlt.P.Qx2.hpk_sq', Matrix.one_mul]

theorem hpart1_dec {P Q : Mat k r} (hP : inLie k r P) (hQ : inLie k r Q) :
    hpart1 (Hpk k r) (P + Complex.I • Q) = P := by
  unfold hpart1
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hconj_lie hP, hconj_lie hQ]
  simp only [RCLike.star_def, Complex.conj_I]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  ring

theorem hpart2_dec {P Q : Mat k r} (hP : inLie k r P) (hQ : inLie k r Q) :
    hpart2 (Hpk k r) (P + Complex.I • Q) = Q := by
  unfold hpart2
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hconj_lie hP, hconj_lie hQ]
  simp only [RCLike.star_def, Complex.conj_I]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  field_simp
  ring_nf
  try simp [Complex.I_sq]
  try ring

theorem dec (Z : Mat k r) : Z = hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
  unfold hpart1 hpart2
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  field_simp
  ring

theorem rdV_fun_add {Φ₁ Φ₂ : Mat k r → E} {g X : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g)
    (hgG : g ∈ GV k r) (hX : inLie k r X) (c : ℂ) :
    RdV X (fun x => Φ₁ x + c • Φ₂ x) g = RdV X Φ₁ g + c • RdV X Φ₂ g :=
  (((loc_hasDerivAt le_rfl h₁ hgG hX).add ((loc_hasDerivAt le_rfl h₂ hgG hX).const_smul c))).deriv

theorem rdV_sub' {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) : RdV (X - Y) Φ g = RdV X Φ g - RdV Y Φ g := by
  have hY' : inLie k r (((-1 : ℝ) : ℂ) • Y) := B4.inLie_rsmul hY (-1)
  have e : X - Y = X + ((-1 : ℝ) : ℂ) • Y := by simp [sub_eq_add_neg]
  rw [e, rdV_add hloc hgG hX hY', rdV_rsmul hloc hgG hY]
  simp [sub_eq_add_neg]

theorem loc_add {m : ℕ∞} {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m Φ₁ g) (h₂ : Loc m Φ₂ g) (c : ℂ) :
    Loc m (fun x => Φ₁ x + c • Φ₂ x) g := by
  obtain ⟨U₁, f₁, hU₁, hg₁, hc₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂, hU₂, hg₂, hc₂, he₂⟩ := h₂
  refine ⟨U₁ ∩ U₂, fun x => f₁ x + c • f₂ x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact (hc₁.mono Set.inter_subset_left).add
      ((hc₂.mono Set.inter_subset_right).const_smul (c : ℂ))
  · intro x hx hxG
    show Φ₁ x + c • Φ₂ x = f₁ x + c • f₂ x
    rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]

theorem loc_EZ {m : ℕ∞} {Φ : Mat k r → E} {g : Mat k r} (Z : Mat k r) (h : Loc (m + 1) Φ g) :
    Loc m (EZ Z Φ) g :=
  loc_add (loc_RdV (hermitian_part_mem_lie Z) h) (loc_RdV (antihermitian_part_mem_lie Z) h) Complex.I

theorem EZ_comm {Φ : Mat k r → E} {g : Mat k r} (Z W : Mat k r) (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) :
    EZ Z (EZ W Φ) g - EZ W (EZ Z Φ) g = EZ (Z * W - W * Z) Φ g := by
  set Z1 := hpart1 (Hpk k r) Z
  set Z2 := hpart2 (Hpk k r) Z
  set W1 := hpart1 (Hpk k r) W
  set W2 := hpart2 (Hpk k r) W
  have hZ1 : inLie k r Z1 := hermitian_part_mem_lie Z
  have hZ2 : inLie k r Z2 := antihermitian_part_mem_lie Z
  have hW1 : inLie k r W1 := hermitian_part_mem_lie W
  have hW2 : inLie k r W2 := antihermitian_part_mem_lie W
  have hl1 : Loc 1 Φ g := loc_mono (by norm_num) hloc
  have hl2 : ∀ X, inLie k r X → Loc 1 (RdV X Φ) g := fun X hX => loc_RdV hX (loc_mono (by norm_num) hloc)
  have eW : EZ W Φ = fun x => RdV W1 Φ x + Complex.I • RdV W2 Φ x := rfl
  have eZ : EZ Z Φ = fun x => RdV Z1 Φ x + Complex.I • RdV Z2 Φ x := rfl
  have L : ∀ X Y Y', inLie k r X → inLie k r Y → inLie k r Y' →
      RdV X (fun x => RdV Y Φ x + Complex.I • RdV Y' Φ x) g =
        RdV X (RdV Y Φ) g + Complex.I • RdV X (RdV Y' Φ) g :=
    fun X Y Y' hX hY hY' => rdV_fun_add (hl2 Y hY) (hl2 Y' hY') hgG hX Complex.I
  have hPQ : Z * W - W * Z = ((Z1 * W1 - W1 * Z1) - (Z2 * W2 - W2 * Z2)) +
      Complex.I • ((Z1 * W2 - W2 * Z1) + (Z2 * W1 - W1 * Z2)) := by
    conv_lhs => rw [dec Z, dec W]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, smul_add, smul_sub]
    module
  have hP : inLie k r ((Z1 * W1 - W1 * Z1) - (Z2 * W2 - W2 * Z2)) :=
    B4.inLie_sub (inLie_comm hZ1 hW1) (inLie_comm hZ2 hW2)
  have hQ : inLie k r ((Z1 * W2 - W2 * Z1) + (Z2 * W1 - W1 * Z2)) :=
    B4.inLie_add (inLie_comm hZ1 hW2) (inLie_comm hZ2 hW1)
  have hR : EZ (Z * W - W * Z) Φ g =
      RdV ((Z1 * W1 - W1 * Z1) - (Z2 * W2 - W2 * Z2)) Φ g +
        Complex.I • RdV ((Z1 * W2 - W2 * Z1) + (Z2 * W1 - W1 * Z2)) Φ g := by
    unfold EZ; rw [hPQ, hpart1_dec hP hQ, hpart2_dec hP hQ]
  rw [hR, rdV_sub' hl1 hgG (inLie_comm hZ1 hW1) (inLie_comm hZ2 hW2),
    rdV_add hl1 hgG (inLie_comm hZ1 hW2) (inLie_comm hZ2 hW1),
    ← rdV_comm hloc hgG hZ1 hW1, ← rdV_comm hloc hgG hZ2 hW2, ← rdV_comm hloc hgG hZ1 hW2,
    ← rdV_comm hloc hgG hZ2 hW1]
  show (RdV Z1 (EZ W Φ) g + Complex.I • RdV Z2 (EZ W Φ) g) -
    (RdV W1 (EZ Z Φ) g + Complex.I • RdV W2 (EZ Z Φ) g) = _
  rw [eW, eZ, L Z1 W1 W2 hZ1 hW1 hW2, L Z2 W1 W2 hZ2 hW1 hW2, L W1 Z1 Z2 hW1 hZ1 hZ2,
    L W2 Z1 Z2 hW2 hZ1 hZ2]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  module

end Formalism.FourierDecayAlt.P.LieDecompositionLocal

namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hpart1_add (Z W : Mat k r) : hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  unfold hpart1; rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; module

theorem hpart2_add (Z W : Mat k r) : hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  unfold hpart2; rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; module

theorem EZ_add {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (Z W : Mat k r) :
    EZ (Z + W) Φ g = EZ Z Φ g + EZ W Φ g := by
  unfold EZ
  rw [hpart1_add, hpart2_add, rdV_add hloc hgG (hermitian_part_mem_lie Z) (hermitian_part_mem_lie W), rdV_add hloc hgG (antihermitian_part_mem_lie Z) (antihermitian_part_mem_lie W)]
  module

theorem EZ_rsmul {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (a : ℝ)
    (Z : Mat k r) : EZ ((a : ℂ) • Z) Φ g = (a : ℂ) • EZ Z Φ g := by
  have hd : (a : ℂ) • Z = (a : ℂ) • hpart1 (Hpk k r) Z + Complex.I • ((a : ℂ) • hpart2 (Hpk k r) Z) := by
    conv_lhs => rw [dec Z]
    rw [smul_add, smul_comm (a : ℂ) Complex.I]
  have hP := B4.inLie_rsmul (hermitian_part_mem_lie Z) a
  have hQ := B4.inLie_rsmul (antihermitian_part_mem_lie Z) a
  have e : EZ ((a : ℂ) • Z) Φ g = RdV ((a : ℂ) • hpart1 (Hpk k r) Z) Φ g +
      Complex.I • RdV ((a : ℂ) • hpart2 (Hpk k r) Z) Φ g := by
    unfold EZ; rw [hd, hpart1_dec hP hQ, hpart2_dec hP hQ]
  rw [e, rdV_rsmul hloc hgG (hermitian_part_mem_lie Z), rdV_rsmul hloc hgG (antihermitian_part_mem_lie Z)]
  unfold EZ
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_add, smul_comm (a : ℂ) Complex.I]

theorem EZ_I {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (Z : Mat k r) :
    EZ (Complex.I • Z) Φ g = Complex.I • EZ Z Φ g := by
  have hd : Complex.I • Z = -hpart2 (Hpk k r) Z + Complex.I • hpart1 (Hpk k r) Z := by
    conv_lhs => rw [dec Z]
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have hP := B4.inLie_neg (antihermitian_part_mem_lie Z)
  have e : EZ (Complex.I • Z) Φ g = RdV (-hpart2 (Hpk k r) Z) Φ g +
      Complex.I • RdV (hpart1 (Hpk k r) Z) Φ g := by
    unfold EZ; rw [hd, hpart1_dec hP (hermitian_part_mem_lie Z), hpart2_dec hP (hermitian_part_mem_lie Z)]
  have hneg : RdV (-hpart2 (Hpk k r) Z) Φ g = -RdV (hpart2 (Hpk k r) Z) Φ g := by
    have := rdV_rsmul hloc hgG (antihermitian_part_mem_lie Z) (-1)
    simpa using this
  rw [e, hneg]
  unfold EZ
  rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel

theorem EZ_smul {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (c : ℂ)
    (Z : Mat k r) : EZ (c • Z) Φ g = c • EZ Z Φ g := by
  have hc : c • Z = (c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul]
  rw [hc, EZ_add hloc hgG, EZ_rsmul hloc hgG, EZ_rsmul hloc hgG, EZ_I hloc hgG, smul_smul,
    ← add_smul]
  rw [Complex.re_add_im]

theorem EZ_sum {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (Z : ι → Mat k r) :
    EZ (∑ i ∈ s, c i • Z i) Φ g = ∑ i ∈ s, c i • EZ (Z i) Φ g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := EZ_rsmul hloc hgG 0 (0 : Mat k r)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EZ_add hloc hgG, EZ_smul hloc hgG, ih]

end Formalism.FourierDecayAlt.P.LieDecompositionLocal
