import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

variable {k r : ℕ}

theorem inWb_bvec_wI (j : Fin (k + 1)) : inWb k r (bvec (wI k r j)) := by
  intro i hi
  unfold bvec
  rw [Pi.single_apply, if_neg]
  rintro rfl
  simp [wI] at hi
  omega

def fr (k r : ℕ) (g : Mx k r) : Fin k → Fin (2 * r + k + 1) → ℂ := fun a => g *ᵥ bvec (wI k r a.castSucc)

section Frame

variable {z : Fin (2 * r + k + 1) → ℂ} {g : Mx k r}

theorem fr_frame (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z) : IsFrameOf k r [z] (fr k r g) := by
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · exact Qx8.inWb_mulVec (show g ∈ Glev k r (Fin.last r) from ⟨hgU, fun c _ => hgfix c⟩) (inWb_bvec_wI _)
  · unfold fr
    rw [Qx8.herm_UH hgU, Qx8.herm_wI]
    by_cases h : a = b
    · subst h
      rw [if_pos rfl, if_pos rfl, if_neg (Fin.castSucc_lt_last a).ne]
    · rw [if_neg (fun e => h (Fin.castSucc_injective _ e)), if_neg h]
  · rw [List.mem_singleton] at hv
    subst hv
    unfold fr
    rw [← hgz, Qx8.herm_UH hgU, Qx8.herm_smul_right', Qx8.herm_wI, if_neg (Fin.castSucc_lt_last a).ne, mul_zero]

theorem sig_wI (j : Fin (k + 1)) : GBasic.sig k r (wI k r j) = wI k r j := by
  have := j.isLt
  unfold GBasic.sig
  rw [if_neg (by simp only [wI]; omega)]

theorem sgn_wI_cs (j : Fin k) : GBasic.sgn k r (wI k r j.castSucc) = 1 := by
  have := j.isLt
  unfold GBasic.sgn
  rw [if_neg (by simp only [wI, Fin.val_castSucc]; omega)]

theorem herm_fr (hgU : g ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) (b : Fin k) :
    herm (Hpk k r) v (fr k r g b) = (g⁻¹ *ᵥ v) (wI k r b.castSucc) := by
  unfold fr
  calc herm (Hpk k r) v (g *ᵥ bvec (wI k r b.castSucc))
      = herm (Hpk k r) (g *ᵥ (g⁻¹ *ᵥ v)) (g *ᵥ bvec (wI k r b.castSucc)) := by rw [Qx8.inv_mulVec_uh hgU]
    _ = herm (Hpk k r) (g⁻¹ *ᵥ v) (bvec (wI k r b.castSucc)) := Qx8.herm_UH hgU _ _
    _ = (g⁻¹ *ᵥ v) (wI k r b.castSucc) := by
      rw [Qx8.herm_bvec_right, Qx8.Hpk_mulVec, sig_wI, sgn_wI_cs, one_mul]

theorem single_mulVec_one {n : ℕ} (x y : Fin n) (v : Fin n → ℂ) : Matrix.single x y (1 : ℂ) *ᵥ v = v y • bvec x := by
  rw [Matrix.single_mulVec]
  ext l
  by_cases h : l = x
  · subst h
    simp [bvec]
  · simp [bvec, Pi.single_apply, h]

theorem unitB_fr (hgU : g ∈ UH (Hpk k r)) (a b : Fin k) :
    unitB (Hpk k r) (fr k r g) a b = g * Matrix.single (wI k r a.castSucc) (wI k r b.castSucc) (1 : ℂ) * g⁻¹ := by
  apply SkewHermitianParts.mat_ext_b
  intro p
  rw [Qx8.unitB_mulVec, herm_fr hgU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, single_mulVec_one,
    Matrix.mulVec_smul]
  rfl

end Frame

theorem unitB_adj {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m) :
    (Hpk k r)⁻¹ * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r = unitB (Hpk k r) Bs b a := by
  apply SkewHermitianParts.mat_ext_b
  intro p
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qx8.unitB_mulVec]
  have h1 : (unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ bvec p) =
      herm (Hpk k r) (bvec p) (Bs a) • (Hpk k r *ᵥ Bs b) := by
    funext q
    have e1 : ((unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ bvec p)) q =
        star (herm (Hpk k r) (bvec q) (Bs b)) * (star (Bs a) ⬝ᵥ (Hpk k r *ᵥ bvec p)) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, unitB, Matrix.of_apply, star_mul',
        Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [e1, Qx2.herm_star, Qx8.herm_bvec_right, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  rw [h1, Qx8.hpk_inv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, WeylGroupFacts.hpk_sq, Matrix.one_mulVec]

theorem hpart1_self {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a : Fin m) :
    hpart1 (Hpk k r) (unitB (Hpk k r) Bs a a) = 0 := by
  unfold hpart1
  rw [unitB_adj Bs a a, sub_self, smul_zero]

theorem hpart2_self {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a : Fin m) :
    hpart2 (Hpk k r) (unitB (Hpk k r) Bs a a) = (-Complex.I) • unitB (Hpk k r) Bs a a := by
  unfold hpart2
  rw [unitB_adj Bs a a, ← two_smul ℂ, smul_smul]
  congr 1
  rw [one_div, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul, Complex.inv_I]

def Dg (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

def dθ (k r : ℕ) (θ : Fin k → ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : r ≤ i.val ∧ i.val < r + k then (θ ⟨i.val - r, by omega⟩ : ℂ) * Complex.I else 0

theorem sum_single (θ : Fin k → ℝ) :
    ∑ c : Fin k, ((θ c : ℂ) * Complex.I) • Matrix.single (wI k r c.castSucc) (wI k r c.castSucc) (1 : ℂ) =
      Matrix.diagonal (dθ k r θ) := by
  ext i j
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    unfold dθ
    by_cases hin : r ≤ i.val ∧ i.val < r + k
    · rw [dif_pos hin, Finset.sum_eq_single ⟨i.val - r, by omega⟩]
      · rw [if_pos]
        constructor <;> (apply Fin.ext; simp only [wI, Fin.val_castSucc]; omega)
      · intro c _ hc
        rw [if_neg]
        rintro ⟨h1, -⟩
        apply hc
        apply Fin.ext
        have := congrArg Fin.val h1
        simp only [wI, Fin.val_castSucc] at this
        simp only
        omega
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hin]
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg]
      rintro ⟨h1, -⟩
      apply hin
      have := congrArg Fin.val h1
      have := c.isLt
      simp only [wI, Fin.val_castSucc] at *
      omega
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hij (h1.symm.trans h2)

theorem diag_exp_blockW (θ : Fin k → ℝ) :
    Matrix.diagonal (NormedSpace.exp (dθ k r θ)) = PI.UpqRep.blockW k r (Dg θ) := by
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hi : PI.HwUniqW.InB k r i
  · by_cases hj : PI.HwUniqW.InB k r j
    · rw [PI.HwUniqW.blockW_in _ hi hj]
      unfold Dg
      rw [Matrix.diagonal_apply]
      unfold PI.HwUniqW.InB at hi hj
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl, Pi.coe_exp]
        unfold dθ
        rw [dif_pos hi, ← Complex.exp_eq_exp_ℂ]
      · rw [if_neg hij, if_neg]
        intro h
        apply hij
        apply Fin.ext
        have := congrArg Fin.val h
        simp only at this
        omega
    · rw [PI.HwUniqW.blockW_in_out _ hi hj, if_neg (PI.HwUniqW.ne_of_inB hi hj)]
  · rw [PI.HwUniqW.blockW_out _ hi]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, Pi.coe_exp]
      unfold dθ
      rw [dif_neg (show ¬ (r ≤ i.val ∧ i.val < r + k) from hi), NormedSpace.exp_zero]
    · rw [if_neg hij, if_neg hij]

theorem torus {g : Mx k r} (hgU : g ∈ UH (Hpk k r)) (θ : Fin k → ℝ) :
    NormedSpace.exp (∑ c : Fin k, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) (fr k r g) c c) =
      g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹ := by
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 (WeylGroupFacts.isUnit_of_uh hgU)
  have hs : ∑ c : Fin k, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) (fr k r g) c c =
      g * Matrix.diagonal (dθ k r θ) * g⁻¹ := by
    simp_rw [unitB_fr hgU]
    rw [← sum_single (r := r) θ, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hs, Matrix.exp_conj _ _ hu, Matrix.exp_diagonal, diag_exp_blockW]

theorem Dg_mem (θ : Fin k → ℝ) : Dg θ ∈ PI.UpqRep.Kset (PI.UpqRep.allPos k) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    unfold Dg
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    have e : (starRingEnd ℂ) ((θ a : ℂ) * Complex.I) + (θ a : ℂ) * Complex.I = 0 := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [e, Complex.exp_zero]
  · rw [PI.HwUniqW.Jm_allPos, Matrix.mul_one, Matrix.one_mul]

theorem blockW_uh {h : Matrix (Fin k) (Fin k) ℂ} (hh : hᴴ * h = 1) :
    PI.UpqRep.blockW k r h ∈ UH (Hpk k r) := by
  have c1 : Hpk k r * PI.UpqRep.blockW k r h = PI.UpqRep.blockW k r h * Hpk k r :=
    PI.HwUniqW.Hpk_blockW_comm (k := k) (r := r) h
  show (PI.UpqRep.blockW k r h)ᴴ * Hpk k r * PI.UpqRep.blockW k r h = Hpk k r
  rw [PI.HwUniqW.blockW_conjTranspose, Matrix.mul_assoc, c1, ← Matrix.mul_assoc, PI.HwUniqW.blockW_mul, hh,
    PI.HwUniqW.blockW_one, Matrix.one_mul]

theorem blockW_fix (h : Matrix (Fin k) (Fin k) ℂ) {l : Fin (2 * r + k + 1)} (hl : ¬ PI.HwUniqW.InB k r l) :
    PI.UpqRep.blockW k r h *ᵥ bvec l = bvec l := by
  funext i
  rw [Qx8.mulVec_bvec]
  by_cases hi : PI.HwUniqW.InB k r i
  · rw [PI.HwUniqW.blockW_in_out _ hi hl]
    simp only [bvec, Pi.single_apply]
    rw [if_neg (PI.HwUniqW.ne_of_inB hi hl)]
  · rw [PI.HwUniqW.blockW_out _ hi]
    simp only [bvec, Pi.single_apply]

theorem emb_uw {z : Fin (2 * r + k + 1) → ℂ} {g : Mx k r} (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z) {h : Matrix (Fin k) (Fin k) ℂ} (hh : hᴴ * h = 1) :
    g * PI.UpqRep.blockW k r h * g⁻¹ ∈ UWset k r z := by
  have hgg : ∀ x, g⁻¹ *ᵥ (g *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Qx8.inv_mul_uh hgU, Matrix.one_mulVec]
  have hfix : ∀ x l, ¬ PI.HwUniqW.InB k r l → g *ᵥ bvec l = x → (g * PI.UpqRep.blockW k r h * g⁻¹) *ᵥ x = x := by
    intro x l hl hx
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hx, hgg, blockW_fix h hl]
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hgU (blockW_uh hh)) (WeylGroupFacts.uh_inv hgU), fun a => ⟨?_, ?_⟩, ?_⟩
  · refine hfix _ (eI k r a) ?_ (hgfix a).1
    unfold PI.HwUniqW.InB; simp only [eI]; omega
  · refine hfix _ (esI k r a) ?_ (hgfix a).2
    have := a.isLt
    unfold PI.HwUniqW.InB; simp only [esI]; omega
  · rw [← hgz, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg, Matrix.mulVec_smul, blockW_fix h (by unfold PI.HwUniqW.InB; simp only [wI, Fin.val_last]; omega)]

theorem capChange {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsRepW k r z π) {Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (hB' : IsFrameOf k r [z] Bs') (w : ℂ) : qdet (EB π Bs) w = qdet (EB π Bs') w := by
  set P : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c) with hP
  set Q : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b) with hQ
  have hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c := by
    intro a
    exact HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB' (hB.1 a) (hB.2.2 a z (by simp))
  have hQP : Q * P = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : herm (Hpk k r) (Bs a) (Bs b) = herm (Hpk k r) (∑ c, P c a • Bs' c) (Bs b) := by
      rw [← hexp a]
    rw [HermitianFormSums.herm_lsum, hB.2.1] at h1
    rw [show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hunit : ∀ a b, unitB (Hpk k r) Bs a b =
      ∑ x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
        (P x.1 a * Q b x.2) • unitB (Hpk k r) Bs' x.1 x.2 := by
    intro a b
    rw [Finset.sum_product]
    ext p q
    have h1 : Bs a p = ∑ c, P c a * Bs' c p := by
      have := congrFun (hexp a) p
      rw [Finset.sum_apply] at this
      exact this
    have h2 : herm (Hpk k r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk k r) (bvec q) (Bs' d) := by
      have h3 : herm (Hpk k r) (bvec q) (Bs b) = herm (Hpk k r) (bvec q) (∑ d, P d b • Bs' d) := by
        rw [← hexp b]
      rw [h3, HermitianFormSums.herm_rsum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hP, hQ, Matrix.of_apply, Qx2.herm_star]
    simp only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]
    rw [h1, h2, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hEB : EB π Bs = Econj (EB π Bs') P Q := by
    funext a b
    unfold EB Econj
    rw [hunit a b, (HermitianFormSums.ec_sum elementary_lie_elements hπ _ _ (fun x : Fin k × Fin k => unitB (Hpk k r) Bs' x.1 x.2)
      (fun x => QrD.frame_lie hB' x.1 x.2) _ (QrD.frame_lie hB' a a)).2, Finset.sum_product]
    ext v
    simp
  rw [hEB]
  exact ((contractions_covariant (Module.End ℂ W) k (EB π Bs') P Q
    (frame_general_linear W k r k z π Bs' hπ hB').1 hQP hPQ w 0 0 0 0).1)

end QrCap

end Formalism.FourierDecayAlt.P
