import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SkewHermitianParts

section Closed

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem closedS (S : Submodule ℂ W) : IsClosed (S : Set W) := Submodule.closed_of_finiteDimensional S

theorem deriv_mem (S : Submodule ℂ W) {f : ℝ → W} {f' : W} (h : HasDerivAt f f' 0) (hf : ∀ t, f t ∈ S) : f' ∈ S := by
  have h1 := h.tendsto_slope_zero
  refine (closedS S).mem_of_tendsto h1 (Eventually.of_forall fun t => ?_)
  exact (S.restrictScalars ℝ).smul_mem _ (S.sub_mem (hf _) (hf _))

theorem pow_mem (S : Submodule ℂ W) {A : W →L[ℂ] W} (hA : ∀ v ∈ S, A v ∈ S) (n : ℕ) : ∀ v ∈ S, (A ^ n) v ∈ S := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih =>
    intro v hv
    rw [pow_succ]
    exact ih _ (hA v hv)

theorem exp_mem (S : Submodule ℂ W) {A : W →L[ℂ] W} (hA : ∀ v ∈ S, A v ∈ S) : ∀ v ∈ S, NormedSpace.exp A v ∈ S := by
  intro v hv
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have h2 := (ContinuousLinearMap.apply ℂ W v).hasSum h
  refine (closedS S).mem_of_tendsto h2 (Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  show ((((n.factorial : ℂ)⁻¹) • A ^ n : W →L[ℂ] W)) v ∈ S
  exact S.smul_mem _ (pow_mem S hA n v hv)

end Closed

section Geometry

open AnisotropicColumnSums

variable {k r : ℕ}

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ} {g h : Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) :
    g * h ∈ UWset k r z := by
  have := Qx8.glev_mul (Qx8.uw_glev (Fin.last r) hg) (Qx8.uw_glev (Fin.last r) hh)
  refine ⟨this.1, fun a => this.2 a (by simp), ?_⟩
  rw [← Matrix.mulVec_mulVec, hh.2.2, hg.2.2]

theorem herm_zero_right (v : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v 0 = 0 := by simp [herm]

theorem skew {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (X *ᵥ v) w = -herm (Hpk k r) v (X *ᵥ w) := by
  have e : Hpk k r * X = -(Xᴴ * Hpk k r) := eq_neg_of_add_eq_zero_right hX
  unfold herm
  rw [Matrix.mulVec_mulVec, e, Matrix.neg_mulVec, dotProduct_neg, Matrix.star_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]

theorem lie_inWb {X : Mx k r} (hX : inLieLev k r (Fin.last r) X) (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r (X *ᵥ v) := by
  rw [Qx8.inWb_iff]
  intro c
  have hc := hX.2 c (by simp)
  constructor
  · rw [← Qx8.coord_e (X *ᵥ v) c, skew hX.1, hc.2, herm_zero_right, neg_zero]
  · rw [← Qx8.coord_es (X *ᵥ v) c, skew hX.1, hc.1, herm_zero_right, neg_zero]

theorem complete0 {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    v = ∑ j, (herm (Hpk k r) v (bcol k r x Bs j) * nrm k r x j) • bcol k r x Bs j := by
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => bcol k r x Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (bcol k r x Bs j) * nrm k r x j with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← gram hxx hB j j', ← sum_last (bcol_inWb hx hB j'), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hP, hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hp : Qx2.inV k r (Fin.last r) p
  · obtain ⟨c, rfl⟩ := Qx2.exists_posL hp
    calc v (posL k r (Fin.last r) c) = ∑ d, (P * Q) c d * v (posL k r (Fin.last r) d) := by
          simp [hPQ, Matrix.one_apply]
      _ = ∑ d, ∑ j, P c j * Q j d * v (posL k r (Fin.last r) d) := by
          simp only [Matrix.mul_apply, Finset.sum_mul]
      _ = ∑ j, ∑ d, P c j * Q j d * v (posL k r (Fin.last r) d) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← sum_last hv, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [hP, hQ, Matrix.of_apply]
          ring
  · have hp' : p.val < r ∨ r + k < p.val := by
      unfold Qx2.inV at hp
      simp only [Fin.val_last] at hp
      omega
    rw [hv p hp']
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [bcol_inWb hx hB j p hp', mul_zero]

theorem complete {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    v = ∑ b, herm (Hpk k r) v (Bs b) • Bs b + (herm (Hpk k r) v x * (herm (Hpk k r) x x)⁻¹) • x := by
  conv_lhs => rw [complete0 hx hxx hB hv]
  rw [← Equiv.sum_comp (finCongr (mdim_last (k := k) (r := r)).symm), Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [bcol, nrm]
  · simp [bcol, nrm]

theorem mat_ext_b {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℂ} (h : ∀ p, M *ᵥ bvec p = N *ᵥ bvec p) : M = N := by
  ext i j
  rw [← Qx8.mulVec_bvec M, h, Qx8.mulVec_bvec]

theorem pos_cases (p : Fin (2 * r + k + 1)) :
    (∃ c, p = eI k r c) ∨ (∃ c, p = esI k r c) ∨ inWb k r (bvec p) := by
  by_cases h1 : p.val < r
  · exact Or.inl ⟨⟨p.val, h1⟩, rfl⟩
  · by_cases h2 : r + k < p.val
    · have := p.isLt
      exact Or.inr (Or.inl ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)
    · refine Or.inr (Or.inr fun i hi => ?_)
      have : i ≠ p := by
        rintro rfl
        omega
      simp [bvec, this]

theorem lie_expand {z : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hzz : herm (Hpk k r) z z ≠ 0) (hB : IsFrameOf k r [z] Bs) {X : Mx k r} (hX : InLieW k r z X) :
    X = ∑ a, ∑ b, herm (Hpk k r) (X *ᵥ Bs b) (Bs a) • unitB (Hpk k r) Bs a b := by
  have hR : ∀ v, (∑ a, ∑ b, herm (Hpk k r) (X *ᵥ Bs b) (Bs a) • unitB (Hpk k r) Bs a b) *ᵥ v =
      ∑ a, ∑ b, (herm (Hpk k r) (X *ᵥ Bs b) (Bs a) * herm (Hpk k r) v (Bs b)) • Bs a := by
    intro v
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_mulVec, Qx8.unitB_mulVec, smul_smul]
  have hW : ∀ v, inWb k r v → X *ᵥ v =
      ∑ a, ∑ b, (herm (Hpk k r) (X *ᵥ Bs b) (Bs a) * herm (Hpk k r) v (Bs b)) • Bs a := by
    intro v hv
    have e1 : X *ᵥ v = ∑ b, herm (Hpk k r) v (Bs b) • (X *ᵥ Bs b) := by
      conv_lhs => rw [complete hz hzz hB hv]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hX.2, smul_zero, add_zero, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    have e2 : ∀ b, X *ᵥ Bs b = ∑ a, herm (Hpk k r) (X *ᵥ Bs b) (Bs a) • Bs a := by
      intro b
      conv_lhs => rw [complete hz hzz hB (lie_inWb hX.1 (Bs b))]
      rw [skew hX.1.1 (Bs b) z, hX.2, herm_zero_right]
      simp
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    conv_lhs => rw [e2 b]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, mul_comm (herm (Hpk k r) v (Bs b))]
  apply mat_ext_b
  intro p
  rw [hR]
  rcases pos_cases p with ⟨c, rfl⟩ | ⟨c, rfl⟩ | hp
  · rw [(hX.1.2 c (by simp)).1]
    symm
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [(Qx8.orth_e (hB.1 b) c).1, mul_zero, zero_smul]
  · rw [(hX.1.2 c (by simp)).2]
    symm
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [(Qx8.orth_e (hB.1 b) c).2, mul_zero, zero_smul]
  · exact hW _ hp

theorem hpart1_skew {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) : hpart1 (Hpk k r) X = X := by
  have e : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  unfold hpart1
  rw [Qx8.hpk_inv, Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul,
    sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_skew {X : Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) : hpart2 (Hpk k r) X = 0 := by
  have e : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  unfold hpart2
  rw [Qx8.hpk_inv, Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Qx2.hpk_sq', Matrix.one_mul,
    add_neg_cancel, smul_zero]

theorem inLie_zero (z : Fin (2 * r + k + 1) → ℂ) : InLieW k r z 0 :=
  ⟨⟨by simp, fun a _ => by simp⟩, by simp⟩

theorem inGl_zero (z : Fin (2 * r + k + 1) → ℂ) : InGlW k r z 0 := by
  have h1 : hpart1 (Hpk k r) (0 : Mx k r) = 0 := by simp [hpart1]
  have h2 : hpart2 (Hpk k r) (0 : Mx k r) = 0 := by simp [hpart2]
  unfold InGlW
  rw [h1, h2]
  exact ⟨inLie_zero z, inLie_zero z⟩

end Geometry

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem dOp_zero (π : Mx k r → (W →L[ℂ] W)) : dOp π (0 : Mx k r) = 0 := by
  unfold dOp
  simp

theorem dOp_stab (hE : EcLie) {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
    {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0) (hπ : IsRepW k r z π)
    (hB : IsFrameOf k r [z] Bs) {S : Submodule ℂ W} (hS : Stab (EB π Bs) S) {X : Mx k r} (hX : InLieW k r z X) :
    ∀ v ∈ S, dOp π X v ∈ S := by
  let Gd : Mx k r → Prop := fun Z => InGlW k r z Z ∧ ∀ v ∈ S, ecOp π Z v ∈ S
  have g0 : Gd 0 := by
    refine ⟨inGl_zero z, fun v _ => ?_⟩
    have h := ((hE W k r z π hπ 0 0 (inGl_zero z) (inGl_zero z)).2.1 0).2
    rw [zero_smul, zero_smul] at h
    rw [h]
    exact S.zero_mem
  have gadd : ∀ Z Z', Gd Z → Gd Z' → Gd (Z + Z') := by
    intro Z Z' h h'
    have e := (hE W k r z π hπ Z Z' h.1 h'.1).1
    refine ⟨e.1, fun v hv => ?_⟩
    rw [e.2]
    exact S.add_mem (h.2 v hv) (h'.2 v hv)
  have gsmul : ∀ (c : ℂ) Z, Gd Z → Gd (c • Z) := by
    intro c Z h
    have e := (hE W k r z π hπ Z Z h.1 h.1).2.1 c
    refine ⟨e.1, fun v hv => ?_⟩
    rw [e.2]
    exact S.smul_mem _ (h.2 v hv)
  have gu : ∀ a b, Gd (unitB (Hpk k r) Bs a b) := fun a b => ⟨frame_lie hB a b, fun v hv => hS a b v hv⟩
  have hsum : Gd (∑ a, ∑ b, herm (Hpk k r) (X *ᵥ Bs b) (Bs a) • unitB (Hpk k r) Bs a b) :=
    Finset.sum_induction _ Gd gadd g0 fun a _ =>
      Finset.sum_induction _ Gd gadd g0 fun b _ => gsmul _ _ (gu a b)
  rw [← lie_expand hz hzz hB hX] at hsum
  have e : ecOp π X = dOp π X := by
    unfold ecOp
    rw [hpart1_skew hX.1.1, hpart2_skew hX.1.1, dOp_zero, smul_zero, add_zero]
  rw [← e]
  exact hsum.2

end Rep

end SkewHermitianParts

theorem stabilizer_lie_algebra : Formalism.FourierDecayAlt.Qr.StabLie := by
  intro W _ _ _ k r m z e π Bs hπ hB S hS a b v hv
  have hBz : IsFrameOf k r [z] Bs := Qx8.frame_sub hB (by simp)
  have hl := frame_lie hBz a b
  have hk := Qx8.hpart_kill Bs a b (v := e) (fun c => Qx8.frame_orth hB (by simp) c)
  have key : ∀ X, InLieW k r z X → X *ᵥ e = 0 → dOp π X v ∈ S := by
    intro X hX hXe
    have h := dOp_hasDeriv hπ.1 hπ.2 hX
    have h2 := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    exact SkewHermitianParts.deriv_mem S h2 (fun t => hS _ (exp_uw hX t) (Qx8.exp_fix hXe t) v hv)
  exact S.add_mem (key _ hl.1 hk.1) (S.smul_mem _ (key _ hl.2 hk.2))

theorem qr_lieStab_of : Formalism.FourierDecayAlt.Qr.ExpGen → Formalism.FourierDecayAlt.Qr.PiExp → Formalism.FourierDecayAlt.Qr.EcLie → Formalism.FourierDecayAlt.Qr.LieStab := by
  intro hG hP hE W _ _ _ k r z π Bs hz hT hπ hB S hS h hh
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    rw [Qx8.herm_self']
    intro h0
    rw [neg_eq_zero, Complex.ofReal_eq_zero] at h0
    exact hT.ne' h0
  refine (hG k r z hz hT (fun h => h ∈ UWset k r z ∧ ∀ v ∈ S, π h v ∈ S) ⟨Qx8.uw_one z, fun v hv => ?_⟩ ?_ h hh).2
  · rw [hπ.1.1]
    exact hv
  · intro X g hX hg
    have h1 : NormedSpace.exp X ∈ UWset k r z := by
      have := exp_uw hX 1
      simpa using this
    have h2 : π (NormedSpace.exp X) = NormedSpace.exp (dOp π X) := by
      have := hP W k r z π hπ X hX 1
      simpa using this
    refine ⟨SkewHermitianParts.uw_mul h1 hg.1, fun v hv => ?_⟩
    rw [hπ.1.2 _ h1 _ hg.1, h2]
    exact SkewHermitianParts.exp_mem S (SkewHermitianParts.dOp_stab hE hz hzz hπ hB hS hX) _ (hg.2 v hv)

end Formalism.FourierDecayAlt.P
