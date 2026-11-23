import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact

noncomputable section

open Matrix Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.WFL.HNL

variable {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a a' : ℕ} (h : a ≤ a') : spanLt e a ≤ spanLt e a' :=
  Submodule.span_mono (by rintro _ ⟨b, hb, rfl⟩; exact ⟨b, lt_of_lt_of_le hb h, rfl⟩)

private theorem isClosed_sub_one_mulVec_mem (v : Fin n → ℂ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ v ∈ S} :=
  S.closed_of_finiteDimensional.preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)

theorem isClosed_inN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  simp only [InN, InS, Set.setOf_and, Set.setOf_forall]
  exact ((isClosed_iInter fun a => isClosed_sub_one_mulVec_mem _ _).inter (isClosed_sub_one_mulVec_mem _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_sub_one_mulVec_mem _ _)

theorem mulVec_mem_of {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1)
    (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : g *ᵥ x ∈ spanLt e a := by
  have key : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
    show Submodule.span ℂ _ ≤ _
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.1 < a := hb
    have hsplit : g *ᵥ e b = (g - 1) *ᵥ e b + e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    show Matrix.mulVecLin g (e b) ∈ spanLt e a
    rw [Matrix.mulVecLin_apply, hsplit]
    exact add_mem (spanLt_mono e hb'.le (hg b)) (Submodule.subset_span ⟨b, hb', rfl⟩)
  exact key hx

theorem inv_mulVec_mem_of {g gi : Matrix (Fin n) (Fin n) ℂ} (h1 : g * gi = 1) (h2 : gi * g = 1)
    (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) :
    gi *ᵥ x ∈ spanLt e a := by
  have hmap : ∀ y ∈ spanLt e a, Matrix.mulVecLin g y ∈ spanLt e a := fun y hy => mulVec_mem_of hg a hy
  set φ := (Matrix.mulVecLin g).restrict hmap with hφ
  have hinj : Function.Injective φ := by
    intro u v huv
    have h := congrArg (fun w : spanLt e a => gi *ᵥ (w : Fin n → ℂ)) huv
    simp only [hφ, LinearMap.restrict_coe_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h2,
      Matrix.one_mulVec] at h
    exact Subtype.ext h
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨x, hx⟩
  have hy' : g *ᵥ (y : Fin n → ℂ) = x := by
    have h := congrArg Subtype.val hy
    simpa only [hφ, LinearMap.restrict_coe_apply, Matrix.mulVecLin_apply] using h
  rw [← hy', Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  exact y.2

theorem inN_one (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    InN ε e z (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp

theorem mul_sub_one_mulVec (A B : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (A * B - 1) *ᵥ v = A *ᵥ ((B - 1) *ᵥ v) + (A - 1) *ᵥ v := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  abel

theorem inN_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : InN ε e z A) (hB : InN ε e z B) :
    InN ε e z (A * B) := by
  obtain ⟨⟨hA1, hA2⟩, hA3⟩ := hA
  obtain ⟨⟨hB1, hB2⟩, hB3⟩ := hB
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [mul_sub_one_mulVec]
  · exact add_mem (mulVec_mem_of hA1 _ (hB1 a)) (hA1 a)
  · exact add_mem (mulVec_mem_of hA1 _ hB2) hA2
  · exact add_mem (mulVec_mem_of hA1 _ (hB3 y hy)) (hA3 y hy)

theorem inv_sub_one_mulVec {A Ai : Matrix (Fin n) (Fin n) ℂ} (h : Ai * A = 1) (v : Fin n → ℂ) :
    (Ai - 1) *ᵥ v = -(Ai *ᵥ ((A - 1) *ᵥ v)) := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  abel

theorem inN_inv {A Ai : Matrix (Fin n) (Fin n) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : InN ε e z A) :
    InN ε e z Ai := by
  obtain ⟨⟨hA1, hA2⟩, hA3⟩ := hA
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [inv_sub_one_mulVec h2] <;> refine neg_mem ?_
  · exact inv_mulVec_mem_of h1 h2 hA1 _ (hA1 a)
  · exact inv_mulVec_mem_of h1 h2 hA1 _ hA2
  · exact inv_mulVec_mem_of h1 h2 hA1 _ (hA3 y hy)

theorem fix_of_span {g : Matrix (Fin n) (Fin n) ℂ} (hge : ∀ a, g *ᵥ e a = e a) (a : ℕ) {x : Fin n → ℂ}
    (hx : x ∈ spanLt e a) : g *ᵥ x = x := by
  have h := LinearMap.eqOn_span' (R := ℂ) (f := Matrix.mulVecLin g) (g := LinearMap.id)
    (s := e '' {b | b.1 < a}) (by rintro _ ⟨b, -, rfl⟩; simp [hge b]) hx
  simpa using h

theorem conj_sub_one_mulVec {H M Hi : Matrix (Fin n) (Fin n) ℂ} (h : H * Hi = 1) (v : Fin n → ℂ) :
    (H * M * Hi - 1) *ᵥ v = H *ᵥ ((M - 1) *ᵥ (Hi *ᵥ v)) := by
  simp only [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc, h]

private theorem hJ_mulVec_of_inUJ {H : Matrix (Fin n) (Fin n) ℂ} (hH : Formalism.REAL.inUJ ε H) (x y : Fin n → ℂ) :
    hJ ε (H *ᵥ x) (H *ᵥ y) = hJ ε x y := by
  have hH' : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε := hH
  unfold hJ
  conv_rhs => rw [← hH']
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem inN_conj {H Hi M : Matrix (Fin n) (Fin n) ℂ} (hH : Formalism.REAL.inUJ ε H) (h1 : H * Hi = 1)
    (h2 : Hi * H = 1) (hge : ∀ a, H *ᵥ e a = e a) (hgz : H *ᵥ z = z) (hM : InN ε e z M) :
    InN ε e z (H * M * Hi) := by
  have hHi_e : ∀ a, Hi *ᵥ e a = e a := fun a => by
    conv_lhs => rw [← hge a]
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hHi_z : Hi *ᵥ z = z := by
    conv_lhs => rw [← hgz]
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  obtain ⟨⟨hM1, hM2⟩, hM3⟩ := hM
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [conj_sub_one_mulVec h1]
  · rw [hHi_e, fix_of_span hge _ (hM1 a)]; exact hM1 a
  · rw [hHi_z, fix_of_span hge _ hM2]; exact hM2
  · have hy' : ∀ a, hJ ε (e a) (Hi *ᵥ y) = 0 := fun a => by
      have h := hJ_mulVec_of_inUJ hH (e a) (Hi *ᵥ y)
      rw [hge a, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h
      rw [← h]; exact hy a
    rw [fix_of_span hge _ (hM3 _ hy')]; exact hM3 _ hy'

theorem uMat_mul_inv (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  rw [← Formalism.L2.SG.Pf.Tau.uMat_mul, mul_inv_cancel, Formalism.L2.SG.Pf.Tau.uMat_one]

theorem uMat_inv_mul (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  rw [← Formalism.L2.SG.Pf.Tau.uMat_mul, inv_mul_cancel, Formalism.L2.SG.Pf.Tau.uMat_one]

theorem continuous_uMat : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
  Units.continuous_val.comp continuous_subtype_val

end Formalism.L2.SG.Pf.WFL.HNL

namespace Formalism.L2.SG.Pf.WFL

open Formalism.L2.SG.Pf.WFL.HNL

variable {k r : ℕ}

private theorem hJ_swap_eq_star {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_one, star_neg] <;> ring

private theorem hJ_add_right' {n : ℕ} (ε : Fin n → Bool) (x y y' : Fin n → ℂ) :
    hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

private theorem hJ_smul_right_unitary_haar_products {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) :
    hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem hJ_sub_right_unitary_haar_products {n : ℕ} (ε : Fin n → Bool) (x y y' : Fin n → ℂ) :
    hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_sub, dotProduct_sub]

private theorem hJ_right_sum {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) {ι : Type} (s : Finset ι)
    (v : ι → Fin n → ℂ) : hJ ε x (∑ i ∈ s, v i) = ∑ i ∈ s, hJ ε x (v i) :=
  map_sum (AddMonoidHom.mk' (hJ ε x) (hJ_add_right' ε x)) v s

private theorem colQ_eq_frame_vector (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    (∃ a, colQ e f wf z0 j = e a) ∨ (∃ a, colQ e f wf z0 j = f a) ∨ (∃ b, colQ e f wf z0 j = wf b) ∨
      colQ e f wf z0 j = z0 := by
  unfold colQ
  split_ifs <;> simp

private theorem eq_zero_of_hJ_frame_eq_zero_of_isFrameJ {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    {y : Fin (2 * r + k + 1) → ℂ} (he : ∀ a, hJ ε (e a) y = 0) (hf : ∀ a, hJ ε (f a) y = 0)
    (hw : ∀ b, hJ ε (wf b) y = 0) (hz : hJ ε z0 y = 0) : y = 0 := by
  have hcol : ∀ j, hJ ε (colQ e f wf z0 j) y = 0 := fun j => by
    rcases colQ_eq_frame_vector e f wf z0 j with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨b, hb⟩ | h0
    · rw [ha]; exact he a
    · rw [ha]; exact hf a
    · rw [hb]; exact hw b
    · rw [h0]; exact hz
  have hv : (Qm e f wf z0)ᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
    funext j
    calc ((Qm e f wf z0)ᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y)) j = hJ ε (colQ e f wf z0 j) y := by
          simp only [Qm, hJ, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply,
            Pi.star_apply]
      _ = 0 := hcol j
  have h1 : Qm e f wf z0 * Qi ε e f wf z0 = 1 := Qm_mul_Qi hF
  unfold Qi at h1
  calc y = (Qm e f wf z0 * (Formalism.QuantumDeterminants.Hpk k r * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε)) *ᵥ y := by
        rw [h1, Matrix.one_mulVec]
    _ = 0 := by
        rw [Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, Matrix.mulVec_zero]

private theorem eq_frame_expansion_of_isFrameJ {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (x : Fin (2 * r + k + 1) → ℂ) :
    x = ∑ a, hJ ε (f a) x • e a + ∑ a, hJ ε (e a) x • f a - hJ ε z0 x • z0 +
      ∑ b, hJ ε (wf b) x • wf b := by
  obtain ⟨ee, ff, ef, ez, fz, zz, ww, ew, fw, zw⟩ := hF
  have hfe : ∀ c a, hJ ε (f c) (e a) = if c = a then 1 else 0 := fun c a => by
    rw [hJ_swap_eq_star, ef]
    by_cases h : a = c
    · subst h; simp
    · simp [h, Ne.symm h]
  have hze : ∀ a, hJ ε z0 (e a) = 0 := fun a => by rw [hJ_swap_eq_star, ez]; simp
  have hzf : ∀ a, hJ ε z0 (f a) = 0 := fun a => by rw [hJ_swap_eq_star, fz]; simp
  have hwe : ∀ b a, hJ ε (wf b) (e a) = 0 := fun b a => by rw [hJ_swap_eq_star, ew]; simp
  have hwf : ∀ b a, hJ ε (wf b) (f a) = 0 := fun b a => by rw [hJ_swap_eq_star, fw]; simp
  have hwz : ∀ b, hJ ε (wf b) z0 = 0 := fun b => by rw [hJ_swap_eq_star, zw]; simp
  have key := eq_zero_of_hJ_frame_eq_zero_of_isFrameJ ⟨ee, ff, ef, ez, fz, zz, ww, ew, fw, zw⟩
    (y := x - (∑ a, hJ ε (f a) x • e a + ∑ a, hJ ε (e a) x • f a - hJ ε z0 x • z0 +
      ∑ b, hJ ε (wf b) x • wf b))
    (fun c => by simp [hJ_sub_right_unitary_haar_products, hJ_add_right', hJ_right_sum, hJ_smul_right_unitary_haar_products, ee, ef, ez, ew])
    (fun c => by simp [hJ_sub_right_unitary_haar_products, hJ_add_right', hJ_right_sum, hJ_smul_right_unitary_haar_products, hfe, ff, fz, fw])
    (fun c => by simp [hJ_sub_right_unitary_haar_products, hJ_add_right', hJ_right_sum, hJ_smul_right_unitary_haar_products, hwe, hwf, hwz, ww])
    (by simp [hJ_sub_right_unitary_haar_products, hJ_add_right', hJ_right_sum, hJ_smul_right_unitary_haar_products, hze, hzf, zz, zw])
  exact sub_eq_zero.mp key

private theorem hJ_self_eq_frame_parseval {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (x : Fin (2 * r + k + 1) → ℂ) :
    hJ ε x x = ∑ a, (hJ ε (f a) x * star (hJ ε (e a) x) + hJ ε (e a) x * star (hJ ε (f a) x)) -
      hJ ε z0 x * star (hJ ε z0 x) + ∑ b, hJ ε (wf b) x * star (hJ ε (wf b) x) := by
  have hs : ∀ v, hJ ε x v = star (hJ ε v x) := fun v => hJ_swap_eq_star ε v x
  rw [congrArg (hJ ε x) (eq_frame_expansion_of_isFrameJ hF x)]
  simp only [hJ_sub_right_unitary_haar_products, hJ_add_right', hJ_right_sum, hJ_smul_right_unitary_haar_products]
  simp only [hs]
  rw [Finset.sum_add_distrib]

private theorem norm_mulVec_apply_le_frame_bound {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    {G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hG : Formalism.REAL.inUJ ε G) (he : ∀ a, G *ᵥ e a = e a)
    (hf : ∀ a, G *ᵥ f a = f a) (hz0 : G *ᵥ z0 = z0) (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    ‖(G *ᵥ x) i‖ ≤ (∑ a, ‖hJ ε (f a) x‖ + ∑ a, ‖hJ ε (e a) x‖ + ‖hJ ε z0 x‖ +
      Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x))) *
      (∑ a, ‖e a i‖ + ∑ a, ‖f a i‖ + ‖z0 i‖ + ∑ b, ‖wf b i‖) := by
  have hinv : ∀ v, G *ᵥ v = v → hJ ε v (G *ᵥ x) = hJ ε v x := fun v hv => by
    have h := HNL.hJ_mulVec_of_inUJ hG v x
    rwa [hv] at h
  have hW : (∑ b, hJ ε (wf b) (G *ᵥ x) * star (hJ ε (wf b) (G *ᵥ x))) =
      ∑ b, hJ ε (wf b) x * star (hJ ε (wf b) x) := by
    have h1 := hJ_self_eq_frame_parseval hF (G *ᵥ x)
    have h2 := hJ_self_eq_frame_parseval hF x
    rw [HNL.hJ_mulVec_of_inUJ hG] at h1
    simp only [hinv _ (he _), hinv _ (hf _), hinv _ hz0] at h1
    rw [h2] at h1
    exact (add_left_cancel h1).symm
  have hWr : (∑ b, Complex.normSq (hJ ε (wf b) (G *ᵥ x))) = ∑ b, Complex.normSq (hJ ε (wf b) x) := by
    rw [Complex.star_def] at hW
    simp only [Complex.mul_conj] at hW
    exact_mod_cast hW
  have n1 : 0 ≤ ∑ a, ‖hJ ε (f a) x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have n2 : 0 ≤ ∑ a, ‖hJ ε (e a) x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have n3 : 0 ≤ ‖hJ ε z0 x‖ := norm_nonneg _
  have n4 : 0 ≤ Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x)) := Real.sqrt_nonneg _
  have hcf : ∀ a, ‖hJ ε (f a) (G *ᵥ x)‖ ≤ ∑ a, ‖hJ ε (f a) x‖ + ∑ a, ‖hJ ε (e a) x‖ + ‖hJ ε z0 x‖ +
      Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x)) := fun a => by
    rw [hinv _ (hf a)]
    have := Finset.single_le_sum (fun a _ => norm_nonneg (hJ ε (f a) x)) (Finset.mem_univ a)
    linarith
  have hce : ∀ a, ‖hJ ε (e a) (G *ᵥ x)‖ ≤ ∑ a, ‖hJ ε (f a) x‖ + ∑ a, ‖hJ ε (e a) x‖ + ‖hJ ε z0 x‖ +
      Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x)) := fun a => by
    rw [hinv _ (he a)]
    have := Finset.single_le_sum (fun a _ => norm_nonneg (hJ ε (e a) x)) (Finset.mem_univ a)
    linarith
  have hcz : ‖hJ ε z0 (G *ᵥ x)‖ ≤ ∑ a, ‖hJ ε (f a) x‖ + ∑ a, ‖hJ ε (e a) x‖ + ‖hJ ε z0 x‖ +
      Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x)) := by
    rw [hinv _ hz0]
    linarith
  have hcw : ∀ b, ‖hJ ε (wf b) (G *ᵥ x)‖ ≤ ∑ a, ‖hJ ε (f a) x‖ + ∑ a, ‖hJ ε (e a) x‖ + ‖hJ ε z0 x‖ +
      Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x)) := fun b => by
    have h1 : ‖hJ ε (wf b) (G *ᵥ x)‖ ≤ Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) x)) := by
      rw [← hWr]
      calc ‖hJ ε (wf b) (G *ᵥ x)‖ = Real.sqrt (‖hJ ε (wf b) (G *ᵥ x)‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (Complex.normSq (hJ ε (wf b) (G *ᵥ x))) := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ _ := Real.sqrt_le_sqrt
            (Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (hJ ε (wf b) (G *ᵥ x)))
              (Finset.mem_univ b))
    linarith
  have hd := congrFun (eq_frame_expansion_of_isFrameJ hF (G *ᵥ x)) i
  simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hd
  rw [hd]
  have h4 : ∀ p q s t : ℂ, ‖p + q - s + t‖ ≤ ‖p‖ + ‖q‖ + ‖s‖ + ‖t‖ := fun p q s t =>
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  refine (h4 _ _ _ _).trans ?_
  rw [mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hcf a) (norm_nonneg (e a i))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hce a) (norm_nonneg (f a i))
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hcz (norm_nonneg (z0 i))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hcw b) (norm_nonneg (wf b i))

private theorem exists_entry_bound_of_fixes_frame {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0) :
    ∃ C : ℝ, ∀ G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Formalism.REAL.inUJ ε G →
      (∀ a, G *ᵥ e a = e a) → (∀ a, G *ᵥ f a = f a) → G *ᵥ z0 = z0 → ∀ i j, ‖G i j‖ ≤ C := by
  refine ⟨∑ j, ∑ i, (∑ a, ‖hJ ε (f a) (Pi.single j 1)‖ + ∑ a, ‖hJ ε (e a) (Pi.single j 1)‖ +
      ‖hJ ε z0 (Pi.single j 1)‖ + Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) (Pi.single j 1)))) *
      (∑ a, ‖e a i‖ + ∑ a, ‖f a i‖ + ‖z0 i‖ + ∑ b, ‖wf b i‖), fun G hG he hf hz0 i j => ?_⟩
  have h := norm_mulVec_apply_le_frame_bound hF hG he hf hz0 (Pi.single j 1) i
  rw [Matrix.mulVec_single_one] at h
  change ‖G i j‖ ≤ _ at h
  have key : ∀ T : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ, (∀ j' i', 0 ≤ T j' i') →
      T j i ≤ ∑ j', ∑ i', T j' i' := fun T hT =>
    (Finset.single_le_sum (f := fun i' => T j i') (fun i' _ => hT j i') (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun j' => ∑ i', T j' i') (fun j' _ => Finset.sum_nonneg fun i' _ => hT j' i')
        (Finset.mem_univ j))
  refine h.trans (key (fun j' i' => (∑ a, ‖hJ ε (f a) (Pi.single j' 1)‖ + ∑ a, ‖hJ ε (e a) (Pi.single j' 1)‖ +
      ‖hJ ε z0 (Pi.single j' 1)‖ + Real.sqrt (∑ b, Complex.normSq (hJ ε (wf b) (Pi.single j' 1)))) *
      (∑ a, ‖e a i'‖ + ∑ a, ‖f a i'‖ + ‖z0 i'‖ + ∑ b, ‖wf b i'‖)) fun j' i' => ?_)
  positivity

theorem frameFix_isCompact {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 z : Fin (2 * r + k + 1) → ℂ} {c : ℂ}
    (hF : IsFrameJ ε e f wf z0) (hz : z0 = c • z) :
    IsCompact {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧
      uMat g *ᵥ z = z} := by
  obtain ⟨C, hC⟩ := exists_entry_bound_of_fixes_frame hF
  have hfixz : ∀ G : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, G *ᵥ z = z → G *ᵥ z0 = z0 :=
    fun G h => by rw [hz, Matrix.mulVec_smul, h]
  have hinvfix : ∀ (g : Formalism.REAL.UJ ε) (v : Fin (2 * r + k + 1) → ℂ), uMat g *ᵥ v = v → uMat g⁻¹ *ᵥ v = v :=
    fun g v h => by
      conv_lhs => rw [← h]
      rw [Matrix.mulVec_mulVec, uMat_inv_mul, Matrix.one_mulVec]
  have hclosed : IsClosed {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧
      uMat g *ᵥ z = z} := by
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (isClosed_iInter fun a => ?_).inter ((isClosed_iInter fun a => ?_).inter ?_) <;>
      exact isClosed_eq (continuous_uMat.matrix_mulVec continuous_const) continuous_const
  have hB : IsCompact {A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j, ‖A i j‖ ≤ C} := by
    have h := isCompact_univ_pi fun (_ : Fin (2 * r + k + 1)) => isCompact_univ_pi fun (_ : Fin (2 * r + k + 1)) =>
      isCompact_closedBall (0 : ℂ) C
    have heq : {A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j, ‖A i j‖ ≤ C} =
        Set.univ.pi fun (_ : Fin (2 * r + k + 1)) => Set.univ.pi fun (_ : Fin (2 * r + k + 1)) => Metric.closedBall (0 : ℂ) C := by
      refine Set.ext fun A => ⟨fun hA => Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => ?_,
        fun hA i j => ?_⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using hA i j
      · have h' := Set.mem_univ_pi.mp (Set.mem_univ_pi.mp hA i) j
        simpa [Metric.mem_closedBall, dist_zero_right] using h'
    rw [heq]
    exact h
  have hTc : IsClosed {p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ Formalism.REAL.inUJ ε p.1} :=
    (isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const).inter
      ((isClosed_eq (continuous_snd.matrix_mul continuous_fst) continuous_const).inter
        (isClosed_eq ((continuous_fst.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
          continuous_fst) continuous_const))
  have hK := (hB.prod hB).inter_right hTc
  haveI := isCompact_iff_compactSpace.mp hK
  let ψ : ↥({A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j, ‖A i j‖ ≤ C} ×ˢ
      {A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j, ‖A i j‖ ≤ C} ∩
      {p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ Formalism.REAL.inUJ ε p.1}) → Formalism.REAL.UJ ε :=
    fun q => ⟨⟨q.1.1, q.1.2, q.2.2.1, q.2.2.2.1⟩, q.2.2.2.2⟩
  have hψ : Continuous ψ := by
    refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val
  refine (isCompact_range hψ).of_isClosed_subset hclosed ?_
  rintro g ⟨he, hf, hzz⟩
  refine ⟨⟨(uMat g, uMat g⁻¹), ⟨⟨?_, ?_⟩, uMat_mul_inv g, uMat_inv_mul g, g.2⟩⟩, ?_⟩
  · exact hC _ g.2 he hf (hfixz _ hzz)
  · exact hC _ (g⁻¹).2 (fun a => hinvfix g _ (he a)) (fun a => hinvfix g _ (hf a))
      (hfixz _ (hinvfix g _ hzz))
  · exact Subtype.ext (Units.ext rfl)

theorem locHNProps_holds : LocHNProps := by
  intro k r ε e f wf z0 z c hF hc hz
  refine ⟨(isClosed_inN ε e z).preimage continuous_uMat, frameFix_isCompact hF hz, ⟨?_, ?_, ?_⟩, ?_⟩
  · show InN ε e z (uMat 1)
    rw [Formalism.L2.SG.Pf.Tau.uMat_one]; exact inN_one ε e z
  · intro a ha b hb
    show InN ε e z (uMat (a * b))
    rw [Formalism.L2.SG.Pf.Tau.uMat_mul]; exact inN_mul ha hb
  · intro a ha
    exact inN_inv (uMat_mul_inv a) (uMat_inv_mul a) ha
  · rintro h ⟨he, -, hzz⟩ m hm
    rw [Formalism.L2.SG.Pf.Tau.uMat_mul, Formalism.L2.SG.Pf.Tau.uMat_mul]
    exact inN_conj h.2 (uMat_mul_inv h) (uMat_inv_mul h) he hzz hm

end Formalism.L2.SG.Pf.WFL
