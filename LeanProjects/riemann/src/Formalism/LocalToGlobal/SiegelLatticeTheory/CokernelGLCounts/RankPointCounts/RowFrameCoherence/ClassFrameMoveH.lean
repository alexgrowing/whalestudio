import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO3FrameValTrans
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation

noncomputable section

open Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

namespace Formalism.L2.SG.Pf.RowForm

namespace ClassFrameUnitaryMoves

variable {n r k : ℕ}

def wm (ε : Fin n → Bool) (wb : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => hJ ε (wb i) (M *ᵥ wb j)

variable {ε : Fin n → Bool}

theorem uMat_mul_ (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem uMat_mul_inv_ (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by simp [uMat]

theorem uMat_inv_mul_ (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by simp [uMat]

theorem cancel_ (g : Formalism.REAL.UJ ε) (w : Fin n → ℂ) : uMat g *ᵥ (uMat g⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, uMat_mul_inv_, one_mulVec]

theorem hJ_adj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g *ᵥ y) = hJ ε (uMat g⁻¹ *ᵥ x) y := by
  rw [← PtRepPf.hJ_UJ ε g (uMat g⁻¹ *ᵥ x) y, cancel_]

theorem fix_inv (g : Formalism.REAL.UJ ε) {x : Fin n → ℂ} (h : uMat g *ᵥ x = x) : uMat g⁻¹ *ᵥ x = x := by
  calc uMat g⁻¹ *ᵥ x = uMat g⁻¹ *ᵥ (uMat g *ᵥ x) := by rw [h]
    _ = x := by rw [mulVec_mulVec, uMat_inv_mul_, one_mulVec]

theorem hJ_span_zero (w : Fin n → ℂ) {S : Set (Fin n → ℂ)} (hS : ∀ y ∈ S, hJ ε w y = 0) {x : Fin n → ℂ}
    (hx : x ∈ Submodule.span ℂ S) : hJ ε w x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact PtRepPf.hJ_zero_right ε w
  | add x y _ _ hx hy => rw [PtRepPf.hJ_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [PtRepPf.hJ_smul_right, hx, mul_zero]

theorem fam_fix {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {M : Matrix (Fin n) (Fin n) ℂ}
    (he : ∀ c, M *ᵥ e c = e c) (hz : M *ᵥ z = z) (b : Fin (r + 1)) : M *ᵥ fam e z b = fam e z b := by
  induction b using Fin.lastCases with
  | last => rw [PtRepPf.fam_last, hz]
  | cast c => rw [PtRepPf.fam_cs, he]

theorem tri (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : InS e z M) :
    ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Q.IsUpperTriangular ∧ (∀ b, Q b b = 1) ∧
      ∀ b, M *ᵥ fam e z b = ∑ c, Q c b • fam e z c := by
  have hmem : ∀ b : Fin (r + 1), (M - 1) *ᵥ fam e z b ∈ Submodule.span ℂ (fam e z '' {c | c < b}) := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [PtRepPf.fam_last]
      refine Submodule.span_mono ?_ hM.2
      rintro _ ⟨c, -, rfl⟩
      exact ⟨Fin.castSucc c, Fin.castSucc_lt_last c, PtRepPf.fam_cs e z c⟩
    | cast a =>
      rw [PtRepPf.fam_cs]
      refine Submodule.span_mono ?_ (hM.1 a)
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨Fin.castSucc c, Fin.castSucc_lt_castSucc_iff.2 hc, PtRepPf.fam_cs e z c⟩
  choose l hl hlx using fun b => (Finsupp.mem_span_image_iff_linearCombination (R := ℂ)).1 (hmem b)
  have hz : ∀ b c, ¬ c < b → l b c = 0 := fun b c hc => by
    by_contra h
    have h2 := hl b
    rw [Finsupp.mem_supported] at h2
    exact hc (h2 (Finsupp.mem_support_iff.2 h))
  refine ⟨Matrix.of fun c b => (if c = b then (1 : ℂ) else 0) + l b c, ?_, ?_, ?_⟩
  · intro i j hji
    have hji' : j < i := hji
    rw [Matrix.of_apply, if_neg (ne_of_lt hji').symm, hz j i (not_lt.2 hji'.le), add_zero]
  · intro b
    rw [Matrix.of_apply, if_pos rfl, hz b b (lt_irrefl b), add_zero]
  · intro b
    have e1 : M *ᵥ fam e z b = fam e z b + (M - 1) *ᵥ fam e z b := by
      rw [sub_mulVec, one_mulVec]; abel
    rw [e1, ← hlx b, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (fam e z i))]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem col_last (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQ : Q.IsUpperTriangular) (hd : ∀ b, Q b b = 1) :
    Qᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
  funext d
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, conjTranspose_apply]
  by_cases h : d = Fin.last r
  · subst h; rw [hd, star_one, if_pos rfl]
  · have h0 : Q (Fin.last r) d = 0 := hQ (lt_of_le_of_ne (Fin.le_last d) h)
    rw [h0, star_zero, if_neg h]

theorem row_last (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQ : Q.IsUpperTriangular) (hd : ∀ b, Q b b = 1) :
    Pi.single (Fin.last r) 1 ᵥ* Q = Pi.single (Fin.last r) 1 := by
  funext c
  simp only [vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h : c = Fin.last r
  · subst h; rw [hd, if_pos rfl]
  · have h0 : Q (Fin.last r) c = 0 := hQ (lt_of_le_of_ne (Fin.le_last c) h)
    rw [h0, if_neg h]

theorem tri_adj (Z Q Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQt : Q.IsUpperTriangular) (hQd : ∀ b, Q b b = 1)
    (hQt' : Q'.IsUpperTriangular) (hQd' : ∀ b, Q' b b = 1) :
    (Q' * adjugate (Qᴴ * Z * Q')) *ᵥ Pi.single (Fin.last r) 1 = adjugate Z *ᵥ Pi.single (Fin.last r) 1 ∧
      Pi.single (Fin.last r) 1 ᵥ* (adjugate (Qᴴ * Z * Q') * Qᴴ) = Pi.single (Fin.last r) 1 ᵥ* adjugate Z ∧
      (Qᴴ * Z * Q').det = Z.det := by
  have hQdet : Q.det = 1 := by rw [det_of_isUpperTriangular hQt]; simp [hQd]
  have hQdet' : Q'.det = 1 := by rw [det_of_isUpperTriangular hQt']; simp [hQd']
  have hcolQ : Qᴴ *ᵥ Pi.single (Fin.last r) (1 : ℂ) = Pi.single (Fin.last r) 1 := col_last Q hQt hQd
  have hrowQ : Pi.single (Fin.last r) (1 : ℂ) ᵥ* Q' = Pi.single (Fin.last r) 1 := row_last Q' hQt' hQd'
  have hA1 : adjugate Qᴴ * Qᴴ = 1 := by rw [adjugate_mul, det_conjTranspose, hQdet, star_one, one_smul]
  have hA2 : Q' * adjugate Q' = 1 := by rw [mul_adjugate, hQdet', one_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [adjugate_mul_distrib, adjugate_mul_distrib, ← Matrix.mul_assoc, hA2, Matrix.one_mul, ← mulVec_mulVec]
    congr 1
    conv_lhs => rw [← hcolQ]
    rw [mulVec_mulVec, hA1, one_mulVec]
  · have hs : Pi.single (Fin.last r) (1 : ℂ) ᵥ* adjugate Q' = Pi.single (Fin.last r) 1 := by
      conv_lhs => rw [← hrowQ]
      rw [vecMul_vecMul, hA2, vecMul_one]
    rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc, hA1, Matrix.mul_one,
      ← vecMul_vecMul, hs]
  · rw [det_mul, det_mul, det_conjTranspose, hQdet, hQdet', star_one, one_mul, mul_one]

theorem Dl_full (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos le_rfl]
  rfl

theorem xPr_move (Z₂ Z Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (G₂ G Nm Am : Matrix (Fin n) (Fin n) ℂ)
    (f' : Fin (r + 1) → Fin n → ℂ) (hG : ∀ b, G₂ *ᵥ f' b = Nm *ᵥ (Am *ᵥ ∑ c, Q' c b • (G *ᵥ f' c)))
    (hc : (Q' * adjugate Z₂) *ᵥ Pi.single (Fin.last r) 1 = adjugate Z *ᵥ Pi.single (Fin.last r) 1) :
    xPr Z₂ G₂ f' = Nm *ᵥ (Am *ᵥ xPr Z G f') := by
  have hc' : ∀ c, ∑ b, adjugate Z₂ b (Fin.last r) * Q' c b = adjugate Z c (Fin.last r) := fun c => by
    have h := congrFun hc c
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.mul_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  unfold xPr
  simp only [hG, mulVec_sum, mulVec_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul, hc' c]

theorem xUn_move (Z₂ Z Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Ni Ai : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin (r + 1) → Fin n → ℂ) (hQ : ∀ b, Ni *ᵥ f b = ∑ c, Q c b • f c) (hA : ∀ b, Ai *ᵥ f b = f b)
    (hr : Pi.single (Fin.last r) 1 ᵥ* (adjugate Z₂ * Qᴴ) = Pi.single (Fin.last r) 1 ᵥ* adjugate Z) :
    Ai *ᵥ (Ni *ᵥ xUn Z₂ f) = xUn Z f := by
  have hr' : ∀ d, ∑ a, star (adjugate Z₂ (Fin.last r) a) * Q d a = star (adjugate Z (Fin.last r) d) := by
    intro d
    have h := congrFun hr d
    simp only [vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.mul_apply, conjTranspose_apply] at h
    rw [← h, star_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [star_mul', star_star]
  unfold xUn
  simp only [mulVec_sum, mulVec_smul, hQ, Finset.smul_sum, smul_smul, hA]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, hr' d]

theorem xPr_perp (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (f' : Fin (r + 1) → Fin n → ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin r) : hJ ε (e c) (xPr (Zhat ε (fam e z) f' G) G f') = 0 := by
  have h1 := congrFun₂ (mul_adjugate (Zhat ε (fam e z) f' G)) (Fin.castSucc c) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last c).ne, smul_zero] at h1
  unfold xPr
  rw [PtRepPf.hJ_sum_right, ← h1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [PtRepPf.hJ_smul_right, ← PtRepPf.fam_cs e z c]
  exact mul_comm _ _

theorem xUn_perp (f : Fin (r + 1) → Fin n → ℂ) (e' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (g : Formalism.REAL.UJ ε)
    (c : Fin r) : hJ ε (e' c) (uMat g⁻¹ *ᵥ xUn (Zhat ε f (fam e' z') (uMat g)) f) = 0 := by
  have h1 := congrFun₂ (adjugate_mul (Zhat ε f (fam e' z') (uMat g))) (Fin.last r) (Fin.castSucc c)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last c).ne', smul_zero] at h1
  rw [hJ_adj, inv_inv]
  unfold xUn
  rw [PtRepPf.hJ_sum_right]
  calc ∑ a, hJ ε (uMat g *ᵥ e' c) (star (adjugate (Zhat ε f (fam e' z') (uMat g)) (Fin.last r) a) • f a)
      = star (∑ a, adjugate (Zhat ε f (fam e' z') (uMat g)) (Fin.last r) a *
          Zhat ε f (fam e' z') (uMat g) a (Fin.castSucc c)) := by
        rw [star_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [PtRepPf.hJ_smul_right, star_mul', ← PtRepPf.hJ_conj, ← PtRepPf.fam_cs e' z' c]
        rfl
    _ = 0 := by rw [h1, star_zero]

theorem pair_na (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (nn a : Formalism.REAL.UJ ε)
    (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQ : ∀ b, uMat nn⁻¹ *ᵥ fam e z b = ∑ c, Q c b • fam e z c)
    (ha : ∀ b, uMat a *ᵥ fam e z b = fam e z b) (b : Fin (r + 1)) (y : Fin n → ℂ) :
    hJ ε (fam e z b) (uMat nn *ᵥ (uMat a *ᵥ y)) = ∑ d, star (Q d b) * hJ ε (fam e z d) y := by
  rw [hJ_adj, hJ_adj, hQ, mulVec_sum, PtRepPf.hJ_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mulVec_smul, fix_inv a (ha d), PtRepPf.hJ_smul_left]

theorem dot_self_ (y : Fin k → ℂ) : ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem eN_unitary (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin k → ℂ) :
    eN (U *ᵥ y) = eN y := by
  have hUU : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  have h : ((∑ i, ‖(U *ᵥ y) i‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) := by
    rw [dot_self_, dot_self_, star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.star_eq_conjTranspose, hUU,
      vecMul_one]
  unfold eN
  rw [Complex.ofReal_injective h]

section Fr

variable (F : PtRepPf.Fr ε r k)

theorem wCoord_fix (M : Matrix (Fin n) (Fin n) ℂ) (he : ∀ c, M *ᵥ F.e c = F.e c)
    (hf : ∀ c, M *ᵥ F.fd c = F.fd c) (hz : M *ᵥ F.z = F.z) (x : Fin n → ℂ) :
    wCoord ε F.wb (M *ᵥ x) = wm ε F.wb M *ᵥ wCoord ε F.wb x := by
  have hx := PtRepPf.expand_of_dual ε F.bv F.dv F.card_ix F.dual x
  funext i
  have h2 : hJ ε (F.wb i) (M *ᵥ x) = ∑ j, hJ ε (F.dv j) x * hJ ε (F.wb i) (M *ᵥ F.bv j) := by
    conv_lhs => rw [hx]
    rw [mulVec_sum, PtRepPf.hJ_sum_right]
    simp only [mulVec_smul, PtRepPf.hJ_smul_right]
  show hJ ε (F.wb i) (M *ᵥ x) = ∑ j, wm ε F.wb M i j * hJ ε (F.wb j) x
  rw [h2, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [PtRepPf.Fr.bv, PtRepPf.Fr.dv, Sum.elim_inl, Sum.elim_inr, he, hf, hz, F.we, F.wf, F.wz, mul_zero,
    Finset.sum_const_zero, zero_add, Fintype.sum_unique]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem wCoord_N (N : Matrix (Fin n) (Fin n) ℂ) (hN : InN ε F.e F.z N) {x : Fin n → ℂ}
    (hx : ∀ c, hJ ε (F.e c) x = 0) : wCoord ε F.wb (N *ᵥ x) = wCoord ε F.wb x := by
  funext i
  show hJ ε (F.wb i) (N *ᵥ x) = hJ ε (F.wb i) x
  have e1 : N *ᵥ x = x + (N - 1) *ᵥ x := by rw [sub_mulVec, one_mulVec]; abel
  have h0 : hJ ε (F.wb i) ((N - 1) *ᵥ x) = 0 := by
    refine hJ_span_zero (F.wb i) (fun y hy => ?_) (hN.2 x hx)
    obtain ⟨c, -, rfl⟩ := hy
    exact F.we i c
  rw [e1, PtRepPf.hJ_add_right, h0, add_zero]

theorem perp_fix (g : Formalism.REAL.UJ ε) (he : ∀ c, uMat g *ᵥ F.e c = F.e c) {x : Fin n → ℂ}
    (hx : ∀ c, hJ ε (F.e c) x = 0) (c : Fin r) : hJ ε (F.e c) (uMat g *ᵥ x) = 0 := by
  rw [← he c, PtRepPf.hJ_UJ, hx]

theorem wm_unitary (g : Formalism.REAL.UJ ε) (he : ∀ c, uMat g *ᵥ F.e c = F.e c) (hz : uMat g *ᵥ F.z = F.z) :
    wm ε F.wb (uMat g) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  have hzw : ∀ m, hJ ε F.z (uMat g *ᵥ F.wb m) = 0 := fun m => by rw [← hz, PtRepPf.hJ_UJ, F.zw]
  have hew : ∀ m c, hJ ε (F.e c) (uMat g *ᵥ F.wb m) = 0 := fun m c => by rw [← he c, PtRepPf.hJ_UJ, F.ew]
  have hp := F.pair (uMat g *ᵥ F.wb j) (uMat g *ᵥ F.wb l) (hew j) (hew l)
  simp only [hzw, mul_zero, zero_mul, star_zero, zero_add] at hp
  rw [PtRepPf.hJ_UJ, F.ww] at hp
  rw [Matrix.mul_apply, Matrix.one_apply, hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.star_apply, wm]
  ring

theorem wm_mul (A H : Matrix (Fin n) (Fin n) ℂ) (he : ∀ c, A *ᵥ F.e c = F.e c) (hf : ∀ c, A *ᵥ F.fd c = F.fd c)
    (hz : A *ᵥ F.z = F.z) : wm ε F.wb (A * H) = wm ε F.wb A * wm ε F.wb H := by
  ext i j
  have h1 := congrFun (wCoord_fix F A he hf hz (H *ᵥ F.wb j)) i
  calc wm ε F.wb (A * H) i j = wCoord ε F.wb (A *ᵥ (H *ᵥ F.wb j)) i := by
        simp only [wm, wCoord, mulVec_mulVec]
    _ = _ := h1
    _ = (wm ε F.wb A * wm ε F.wb H) i j := by
        simp only [mulVec, dotProduct, Matrix.mul_apply, wm, wCoord]

end Fr

theorem move_loc (A B : PtRepPf.Fr ε r k) (i0 i0' : Fin k) (γ nn a nn' a' : Formalism.REAL.UJ ε)
    (hn : InN ε A.e A.z (uMat nn)) (hn' : InN ε B.e B.z (uMat nn'))
    (hae : ∀ c, uMat a *ᵥ A.e c = A.e c) (haf : ∀ c, uMat a *ᵥ A.fd c = A.fd c) (haz : uMat a *ᵥ A.z = A.z)
    (hae' : ∀ c, uMat a' *ᵥ B.e c = B.e c) (haf' : ∀ c, uMat a' *ᵥ B.fd c = B.fd c)
    (haz' : uMat a' *ᵥ B.z = B.z) (H H' : Matrix (Fin k) (Fin k) ℂ)
    (hD : IsDFrame ε (fam A.e A.z) (fam B.e B.z) (uMat γ) (uMat γ⁻¹) A.wb B.wb i0 i0' H H') :
    IsDFrame ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))
      (uMat ((nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹)) A.wb B.wb i0 i0' (wm ε A.wb (uMat a) * H)
      (wm ε B.wb (uMat a') * H') := by
  obtain ⟨hH, hH', hN1, hN2, hU0⟩ := hD
  have haF : ∀ b, uMat a *ᵥ fam A.e A.z b = fam A.e A.z b := fam_fix hae haz
  have haF' : ∀ b, uMat a' *ᵥ fam B.e B.z b = fam B.e B.z b := fam_fix hae' haz'
  have haiF : ∀ b, uMat a⁻¹ *ᵥ fam A.e A.z b = fam A.e A.z b := fun b => fix_inv a (haF b)
  have haiF' : ∀ b, uMat a'⁻¹ *ᵥ fam B.e B.z b = fam B.e B.z b := fun b => fix_inv a' (haF' b)
  obtain ⟨Q, hQt, hQd, hQ⟩ := tri A.e A.z (uMat nn⁻¹)
    (Formalism.L2.SG.RealObj.SpanPreservation.inN_inv ε A.e A.z (uMat nn) (uMat nn⁻¹) (uMat_inv_mul_ nn) hn).1
  obtain ⟨Q', hQt', hQd', hQ'⟩ := tri B.e B.z (uMat nn'⁻¹)
    (Formalism.L2.SG.RealObj.SpanPreservation.inN_inv ε B.e B.z (uMat nn') (uMat nn'⁻¹) (uMat_inv_mul_ nn') hn').1
  obtain ⟨Qn, -, -, hQn⟩ := tri A.e A.z (uMat nn) hn.1
  obtain ⟨Qn', -, -, hQn'⟩ := tri B.e B.z (uMat nn') hn'.1
  have hWa := wm_unitary A a hae haz
  have hWa' := wm_unitary B a' hae' haz'

  have hG2f : ∀ b, uMat (nn * a * γ * a'⁻¹ * nn'⁻¹) *ᵥ fam B.e B.z b =
      uMat nn *ᵥ (uMat a *ᵥ ∑ c, Q' c b • (uMat γ *ᵥ fam B.e B.z c)) := fun b => by
    simp only [uMat_mul_, ← mulVec_mulVec, hQ', mulVec_sum, mulVec_smul, haiF']
  have hZ2 : Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)) =
      Qᴴ * Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ) * Q' := by
    ext i j
    show hJ ε (fam A.e A.z i) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹) *ᵥ fam B.e B.z j) = _
    rw [hG2f, pair_na A.e A.z nn a Q hQ haF]
    simp only [PtRepPf.hJ_sum_right, PtRepPf.hJ_smul_right, Matrix.mul_apply, conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      simp only [Formalism.L2.SG.RealObj.Zhat]; ring
  obtain ⟨hcol, hrow, hdetZ⟩ := tri_adj (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) Q Q' hQt hQd hQt' hQd'
  have hdet : Formalism.L2.SG.RealObj.Dl (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))) (r + 1) =
      Formalism.L2.SG.RealObj.Dl (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (r + 1) := by
    rw [Dl_full, Dl_full, hZ2, hdetZ]

  have hxPr : xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)))
      (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)) (fam B.e B.z) =
      uMat nn *ᵥ (uMat a *ᵥ xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (uMat γ) (fam B.e B.z)) :=
    xPr_move _ _ Q' _ _ _ _ _ hG2f (by rw [hZ2]; exact hcol)
  have hwc1 : wCoord ε A.wb (xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)))
      (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)) (fam B.e B.z)) =
      wm ε A.wb (uMat a) *ᵥ wCoord ε A.wb (xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (uMat γ) (fam B.e B.z)) := by
    rw [hxPr, wCoord_N A _ hn (perp_fix A a hae (fun c => xPr_perp A.e A.z _ _ c)), wCoord_fix A _ hae haf haz]

  have hg2inv : (nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹ = nn' * a' * γ⁻¹ * a⁻¹ * nn⁻¹ := by group
  have hinv : ∀ x, uMat ((nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹) *ᵥ x =
      uMat nn' *ᵥ (uMat a' *ᵥ (uMat γ⁻¹ *ᵥ (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ x)))) := fun x => by
    rw [hg2inv]
    simp only [uMat_mul_, ← mulVec_mulVec]
  have hxUn : uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ
      xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))) (fam A.e A.z)) =
      xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (fam A.e A.z) :=
    xUn_move _ _ Q _ _ _ hQ haiF (by rw [hZ2]; exact hrow)
  have hwc2 : wCoord ε B.wb (uMat ((nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹) *ᵥ
      xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))) (fam A.e A.z)) =
      wm ε B.wb (uMat a') *ᵥ wCoord ε B.wb (uMat γ⁻¹ *ᵥ xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (fam A.e A.z)) := by
    rw [hinv, hxUn, wCoord_N B _ hn' (perp_fix B a' hae' (fun c => xUn_perp _ B.e B.z γ c)),
      wCoord_fix B _ hae' haf' haz']

  have hgrp : nn * a * γ * a'⁻¹ * nn'⁻¹ * nn' * a' = nn * a * γ := by group
  have hmv : ∀ v, uMat (nn * a * γ * a'⁻¹ * nn'⁻¹) *ᵥ (uMat nn' *ᵥ (uMat a' *ᵥ v)) =
      uMat nn *ᵥ (uMat a *ᵥ (uMat γ *ᵥ v)) := fun v => by
    have h := congrArg (fun g => uMat g *ᵥ v) hgrp
    simp only [uMat_mul_, ← mulVec_mulVec] at h ⊢
    exact h
  refine ⟨(Matrix.unitaryGroup (Fin k) ℂ).mul_mem hWa hH, (Matrix.unitaryGroup (Fin k) ℂ).mul_mem hWa' hH', ?_, ?_, ?_⟩
  · rw [hdet, hwc1, ← mulVec_smul, eN_unitary _ hWa, ← mulVec_smul, ← mulVec_mulVec, hN1]
  · rw [hdet, hwc2, ← mulVec_smul, eN_unitary _ hWa', ← mulVec_smul, ← mulVec_mulVec, hN2]
  · intro y hya hyb
    have hy0a : ∀ c, hJ ε (fam A.e A.z c) (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y)) = 0 := by
      intro c
      rw [hJ_adj, inv_inv, haF c, hJ_adj, inv_inv, hQn c, PtRepPf.hJ_sum_left]
      exact Finset.sum_eq_zero fun d _ => by rw [PtRepPf.hJ_smul_left, hya d, mul_zero]
    have hy0b : ∀ b, hJ ε (uMat γ *ᵥ fam B.e B.z b) (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y)) = 0 := by
      intro b
      rw [hJ_adj, inv_inv, hJ_adj, inv_inv, ← hmv, haF' b, hQn' b, mulVec_sum, PtRepPf.hJ_sum_left]
      exact Finset.sum_eq_zero fun c _ => by rw [mulVec_smul, PtRepPf.hJ_smul_left, hyb c, mul_zero]
    have hperp0 : ∀ c, hJ ε (B.e c) (uMat γ⁻¹ *ᵥ (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y))) = 0 := fun c => by
      rw [hJ_adj, inv_inv, ← PtRepPf.fam_cs B.e B.z c]
      exact hy0b _
    have hperpA : ∀ c, hJ ε (A.e c) (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y)) = 0 := fun c => by
      rw [← PtRepPf.fam_cs A.e A.z c]
      exact hy0a _
    have hyy : y = uMat nn *ᵥ (uMat a *ᵥ (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y))) := by
      rw [cancel_ a, cancel_ nn]
    have hWW : ∀ v, star (wm ε B.wb (uMat a')) *ᵥ (wm ε B.wb (uMat a') *ᵥ v) = v := fun v => by
      rw [mulVec_mulVec, (Matrix.mem_unitaryGroup_iff').1 hWa', one_mulVec]
    conv_rhs => rw [hyy]
    rw [wCoord_N A _ hn (perp_fix A a hae hperpA), wCoord_fix A _ hae haf haz, hinv,
      wCoord_N B _ hn' (perp_fix B a' hae' hperp0), wCoord_fix B _ hae' haf' haz', star_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, hWW, hU0 _ hy0a hy0b]

end ClassFrameUnitaryMoves

open ClassFrameUnitaryMoves

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem dFrameMoveHC_holds (u u' : D.what₂.Word) (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) :
    DFrameMoveHC X u u' i0 i0' := by
  intro γ h h' n a n' a' hD hn ha hn' ha'
  unfold Formalism.L2.SG.RealObj.IsDFrameX at hD ⊢
  have hmulH : ∀ w {p q : X.B.I.Ginf}, p ∈ HsetU X w → q ∈ HsetU X w → p * q ∈ HsetU X w := by
    intro w p q hp hq v x hx
    show uMat (p v * q v) *ᵥ rv X.B.I v x = rv X.B.I v x
    rw [uMat_mul_, ← mulVec_mulVec, hq v x hx, hp v x hx]
  refine ⟨hmulH u ha hD.1, hmulH u' ha' hD.2.1, fun v => ?_⟩
  have hfx : ∀ w (p : X.B.I.Ginf), p ∈ HsetU X w →
      (∀ c, uMat (p v) *ᵥ rv X.B.I v (X.eR c) = rv X.B.I v (X.eR c)) ∧
      (∀ c, uMat (p v) *ᵥ rv X.B.I v (X.fR c) = rv X.B.I v (X.fR c)) ∧
      uMat (p v) *ᵥ rv X.B.I v (X.zR w) = rv X.B.I v (X.zR w) := fun w p hp =>
    ⟨fun c => hp v _ (Or.inl (Or.inl ⟨c, rfl⟩)), fun c => hp v _ (Or.inl (Or.inr ⟨c, rfl⟩)), hp v _ (Or.inr rfl)⟩
  obtain ⟨hae, haf, haz⟩ := hfx u a ha
  obtain ⟨hae', haf', haz'⟩ := hfx u' a' ha'
  have hfrm : ∀ w, frm X w 1 v = fam (fun c => rv X.B.I v (X.eR c)) (rv X.B.I v (X.zR w)) := fun w => by
    funext b
    simp [frm, famSc]
  have hmat : ∀ w (p q : X.B.I.Ginf), p ∈ HsetU X w →
      matW X.B.I (X.wfr w v) v (p * q) = wm (X.B.I.ε v) (X.wfr w v) (uMat (p v)) * matW X.B.I (X.wfr w v) v q :=
    fun w p q hp => by
      obtain ⟨he, hf, hz⟩ := hfx w p hp
      exact wm_mul (PtRepPf.frU X w v) (uMat (p v)) (uMat (q v)) he hf hz
  rw [hmat u a h ha, hmat u' a' h' ha', hfrm u, hfrm u']
  have h0 := hD.2.2 v
  rw [hfrm u, hfrm u'] at h0
  exact move_loc (PtRepPf.frU X u v) (PtRepPf.frU X u' v) (i0 v) (i0' v) (γ v) (n v) (a v) (n' v) (a' v)
    (hn v) (hn' v) hae haf haz hae' haf' haz' _ _ h0

end Formalism.L2.SG.Pf.RowForm
