import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKS

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def mOf : {n r k : ℕ} → n = 2 * r + k + 1 → (ε : Fin n → Bool) → (Fin r → Fin n → ℂ) → (Fin r → Fin n → ℂ) →
    (Fin k → Fin n → ℂ) → (Fin n → ℂ) → Formalism.REAL.UJ ε → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
  | _, _, _, rfl, ε, e, f, w, z0, g => Qi ε e f w z0 * uMat g * Qm e f w z0

section Loc

theorem mOf_facts {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    (∀ g g' : Formalism.REAL.UJ ε, mOf hn ε e f w (z0v T z) (g * g') =
      mOf hn ε e f w (z0v T z) g * mOf hn ε e f w (z0v T z) g') ∧
    (∀ g : Formalism.REAL.UJ ε, g ∈ NLoc ε e z → mOf hn ε e f w (z0v T z) g ∈ Nset k r) ∧
    (∀ (g : Formalism.REAL.UJ ε) (b a : Fin r), hJ ε (f b) (uMat g *ᵥ e a) = mOf hn ε e f w (z0v T z) g (eI k r b) (eI k r a)) ∧
    (∀ (g : Formalism.REAL.UJ ε) (b : Fin r) (j : Fin k),
      hJ ε (f b) (uMat g *ᵥ w j) = mOf hn ε e f w (z0v T z) g (eI k r b) (wI k r (Fin.castSucc j))) ∧
    (∀ (g : Formalism.REAL.UJ ε) (b : Fin r),
      hJ ε (f b) (uMat g *ᵥ z) = ((Real.sqrt T : ℝ) : ℂ) * mOf hn ε e f w (z0v T z) g (eI k r b) (wI k r (Fin.last k))) ∧
    (∀ g : Formalism.REAL.UJ ε, g ∈ NLoc ε e z → mL ε e f g = WlocSk.NB.mof (mOf hn ε e f w (z0v T z) g)) := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  have hmem : ∀ g : Formalism.REAL.UJ ε, g ∈ NLoc ε e z → mOf rfl ε e f w (z0v T z) g ∈ Nset k r := fun g hg => by
    have hg' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat g) := by rw [hQz]; exact hg
    exact conj_mem_Nset hFJ hz0 (uMat_mem g) hg'
  have hcol : ∀ (g : Formalism.REAL.UJ ε) b j, hJ ε (f b) (uMat g *ᵥ colQ e f w (z0v T z) j) =
      mOf rfl ε e f w (z0v T z) g (eI k r b) j := fun g b j => hJ_f_col g b j
  refine ⟨fun g g' => ?_, hmem, fun g b a => ?_, fun g b j => ?_, fun g b => ?_, fun g hg => ?_⟩
  · show Qi ε e f w (z0v T z) * uMat (g * g') * Qm e f w (z0v T z) =
      (Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z)) * (Qi ε e f w (z0v T z) * uMat g' * Qm e f w (z0v T z))
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f w (z0v T z) * uMat g) (Qm e f w (z0v T z)) (Qi ε e f w (z0v T z)),
      Qm_mul_Qi hFJ, Matrix.mul_one]
  · rw [← colQ_eI e f w (z0v T z) a, hcol]
  · have hw : colQ e f w (z0v T z) (wI k r (Fin.castSucc j)) = w j := by
      rw [colQ_wI _ _ _ _ _ (show (Fin.castSucc j).val < k from j.isLt)]; rfl
    rw [← hw, hcol]
  · have hz : z = (((Real.sqrt T : ℝ) : ℂ)) • colQ e f w (z0v T z) (wI k r (Fin.last k)) := by
      conv_lhs => rw [← Qm_zB (e := e) (f := f) (wf := w) hT z]
      rw [zBv, Matrix.mulVec_smul, Qm_mulVec_bvec]
    conv_lhs => rw [hz]
    rw [Matrix.mulVec_smul, JL.hJ_smul_r, hcol]
  · have hN := hmem g hg
    set m := mOf rfl ε e f w (z0v T z) g with hm
    have hx : xL ε e f g = WlocSk.NB.bA m := by
      funext b a
      show hJ ε (f b) (uMat g *ᵥ e a) = m (eI k r b) (eI k r a)
      rw [← colQ_eI e f w (z0v T z) a, hcol]
    have ha : aL ε f g = WlocSk.NB.bC m := by
      funext b a
      show hJ ε (f b) (uMat g *ᵥ f a) = m (eI k r b) (esI k r a)
      rw [← colQ_esI e f w (z0v T z) a, hcol]
    have hc := WlocSk.NB.colB_of_mem hN
    have hdet : (WlocSk.NB.bA m).det = 1 := WlocSk.NB.det_of_lowId (WlocSk.NB.lowId_bA hc)
    have hinv : (WlocSk.NB.bA m)⁻¹ = (WlocSk.NB.bF m)ᴴ := by
      rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, WlocSk.NB.adj_eq hc hN.1]
    rw [mL, hx, ha, hinv]
    rfl

end Loc

section BessLaw

variable {ι : Type} {r k : ℕ}

def sclT (T : ℝ) (j : Fin (k + 1)) : ℂ := if j.val < k then 1 else ((Real.sqrt T : ℝ) : ℂ)

theorem sclT_ne {T : ℝ} (hT : 0 < T) (j : Fin (k + 1)) : sclT T j ≠ 0 := by
  unfold sclT
  split_ifs
  · exact one_ne_zero
  · exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hT).ne'

def chAt (T : ℝ) (x : ∀ q : CBlk r, CSpc ι k q) (v : ι) : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) :=
  (fun c => match c with
    | Sum.inl p => (x (Sum.inl (Sum.inl p)) : ι → ℂ) v
    | Sum.inr (Sum.inl (b, j)) => (x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j / sclT T j
    | Sum.inr (Sum.inr p) => (x (Sum.inr (Sum.inl p)) : ι → ℂ) v,
   fun a => (x (Sum.inr (Sum.inr a)) : ι → ℝ) v)

def ph0 (c : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  WlocSk.NB.phi0 c.1 c.2

def Bk (T : ℝ) : ∀ p : CBlk r, (∀ q : CBlk r, CSpc ι k q) → (∀ q : CBlk r, CSpc ι k q) → CSpc ι k p
  | Sum.inl (Sum.inl p) => fun x y v =>
      WlocSk.NB.shG (ph0 (chAt T x v)) (chAt T y v).1 (Sum.inl p) - (x (Sum.inl (Sum.inl p)) : ι → ℂ) v
  | Sum.inl (Sum.inr b) => fun x y v j =>
      sclT T j * WlocSk.NB.shG (ph0 (chAt T x v)) (chAt T y v).1 (Sum.inr (Sum.inl (b, j))) -
        (x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j
  | Sum.inr (Sum.inl p) => fun x y v =>
      WlocSk.NB.shG (ph0 (chAt T x v)) (chAt T y v).1 (Sum.inr (Sum.inr p)) - (x (Sum.inr (Sum.inl p)) : ι → ℂ) v
  | Sum.inr (Sum.inr a) => fun x y v =>
      WlocSk.NB.shH (ph0 (chAt T x v)) (chAt T y v).1 a - (x (Sum.inr (Sum.inr a)) : ι → ℝ) v

def blkOf (T : ℝ) (M : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ∀ p : CBlk r, CSpc ι k p
  | Sum.inl (Sum.inl p) => fun v => WlocSk.NB.psiC (M v) (Sum.inl p)
  | Sum.inl (Sum.inr b) => fun v j => sclT T j * WlocSk.NB.psiC (M v) (Sum.inr (Sum.inl (b, j)))
  | Sum.inr (Sum.inl p) => fun v => WlocSk.NB.psiC (M v) (Sum.inr (Sum.inr p))
  | Sum.inr (Sum.inr a) => fun v => WlocSk.NB.psiR (M v) a

theorem chAt_blkOf {T : ℝ} (hT : 0 < T) (M : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : ι) :
    chAt T (blkOf T M) v = (WlocSk.NB.psiC (M v), WlocSk.NB.psiR (M v)) := by
  refine Prod.ext (funext fun c => ?_) rfl
  rcases c with p | ⟨b, j⟩ | p
  · rfl
  · show sclT T j * WlocSk.NB.psiC (M v) (Sum.inr (Sum.inl (b, j))) / sclT T j = _
    rw [mul_div_cancel_left₀ _ (sclT_ne hT j)]
  · rfl

theorem law_blkOf {T : ℝ} (hT : 0 < T) (M M' : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hM : ∀ v, M v ∈ Nset k r) (hM' : ∀ v, M' v ∈ Nset k r) :
    blkOf T (fun v => M v * M' v) = Formalism.L2.SG.NGCut.SplitEmbedding.mlaw (Bk T) (blkOf T M) (blkOf T M') := by
  have key : ∀ v, WlocSk.NB.psiC (M v * M' v) = WlocSk.NB.psiC (M' v) + WlocSk.NB.shG (M v) (WlocSk.NB.psiC (M' v)) ∧
      WlocSk.NB.psiR (M v * M' v) = WlocSk.NB.psiR (M' v) + WlocSk.NB.shH (M v) (WlocSk.NB.psiC (M' v)) := fun v => by
    have h := WlocSk.NB.lmul_coord (hM v) (WlocSk.NB.psiC (M' v)) (WlocSk.NB.psiR (M' v))
    rwa [WlocSk.NB.nilpotent_chart_left_inverse (hM' v)] at h
  have hph : ∀ v, ph0 (chAt T (blkOf T M) v) = M v := fun v => by
    rw [chAt_blkOf hT]; exact WlocSk.NB.nilpotent_chart_left_inverse (hM v)
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v
    show WlocSk.NB.psiC (M v * M' v) (Sum.inl p) = WlocSk.NB.psiC (M v) (Sum.inl p) + WlocSk.NB.psiC (M' v) (Sum.inl p) +
      (WlocSk.NB.shG (ph0 (chAt T (blkOf T M) v)) (chAt T (blkOf T M') v).1 (Sum.inl p) - WlocSk.NB.psiC (M v) (Sum.inl p))
    rw [hph, chAt_blkOf hT, (key v).1]
    simp only [Pi.add_apply]; ring
  · funext v j
    show sclT T j * WlocSk.NB.psiC (M v * M' v) (Sum.inr (Sum.inl (b, j))) =
      sclT T j * WlocSk.NB.psiC (M v) (Sum.inr (Sum.inl (b, j))) + sclT T j * WlocSk.NB.psiC (M' v) (Sum.inr (Sum.inl (b, j))) +
      (sclT T j * WlocSk.NB.shG (ph0 (chAt T (blkOf T M) v)) (chAt T (blkOf T M') v).1 (Sum.inr (Sum.inl (b, j))) -
        sclT T j * WlocSk.NB.psiC (M v) (Sum.inr (Sum.inl (b, j))))
    rw [hph, chAt_blkOf hT, (key v).1]
    simp only [Pi.add_apply]; ring
  · funext v
    show WlocSk.NB.psiC (M v * M' v) (Sum.inr (Sum.inr p)) = WlocSk.NB.psiC (M v) (Sum.inr (Sum.inr p)) +
      WlocSk.NB.psiC (M' v) (Sum.inr (Sum.inr p)) +
      (WlocSk.NB.shG (ph0 (chAt T (blkOf T M) v)) (chAt T (blkOf T M') v).1 (Sum.inr (Sum.inr p)) -
        WlocSk.NB.psiC (M v) (Sum.inr (Sum.inr p)))
    rw [hph, chAt_blkOf hT, (key v).1]
    simp only [Pi.add_apply]; ring
  · funext v
    show WlocSk.NB.psiR (M v * M' v) a = WlocSk.NB.psiR (M v) a + WlocSk.NB.psiR (M' v) a +
      (WlocSk.NB.shH (ph0 (chAt T (blkOf T M) v)) (chAt T (blkOf T M') v).1 a - WlocSk.NB.psiR (M v) a)
    rw [hph, chAt_blkOf hT, (key v).2]
    simp only [Pi.add_apply]; ring

end BessLaw

section Tri

variable {r k : ℕ}

theorem adj_lowId {A : Matrix (Fin r) (Fin r) ℂ} (hA : WlocSk.NB.LowId A) :
    (∀ a d : Fin r, d < a → A.adjugate a d = 0) ∧ ∀ a, A.adjugate a a = 1 := by
  have hT : A.BlockTriangular id := fun i j hji => by
    have hji' : j < i := hji
    rw [hA i j hji'.le, if_neg (ne_of_gt hji')]
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hT]
    exact Finset.prod_eq_one fun i _ => by rw [hA i i le_rfl, if_pos rfl]
  have hadj : A.adjugate = A⁻¹ := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have hU : IsUnit A.det := by rw [hdet]; exact isUnit_one
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hU
  have hinvT : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨fun a d hda => ?_, fun a => ?_⟩
  · rw [hadj]
    exact hinvT hda
  · rw [hadj]
    have h1 : (A⁻¹ * A) a a = 1 := by rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rw [hA a a le_rfl, if_pos rfl, mul_one] at h1
      exact h1
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with hlt | hgt
      · rw [hinvT hlt, zero_mul]
      · rw [hA c a hgt.le, if_neg hca, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem cF_low (c : WlocSk.NB.CI k r → ℂ) :
    (∀ d a : Fin r, d < a → WlocSk.NB.cF c d a = 0) ∧ ∀ a, WlocSk.NB.cF c a a = 1 := by
  obtain ⟨h1, h2⟩ := adj_lowId (WlocSk.NB.lowId_cA c)
  refine ⟨fun d a hda => ?_, fun a => ?_⟩
  · rw [WlocSk.NB.cF, conjTranspose_apply, h1 a d hda, star_zero]
  · rw [WlocSk.NB.cF, conjTranspose_apply, h2 a, star_one]

theorem tri_conj (F Δ : Matrix (Fin r) (Fin r) ℂ) (hF : ∀ d a, d < a → F d a = 0) (hF1 : ∀ a, F a a = 1)
    (b a : Fin r) (hΔ : ∀ c d : Fin r, b ≤ c → a ≤ d → (c, d) ≠ (b, a) → Δ c d = 0) :
    (Fᴴ * Δ * F) b a = Δ b a := by
  have hFz : ∀ c, c < b → star (F c b) = 0 := fun c hc => by rw [hF c b hc, star_zero]
  have hrow : ∀ d, a ≤ d → (Fᴴ * Δ) b d = if d = a then Δ b a else 0 := by
    intro d hd
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [conjTranspose_apply, hF1, star_one, one_mul]
      split_ifs with hda
      · rw [hda]
      · exact hΔ b d le_rfl hd (fun h => hda (Prod.ext_iff.1 h).2)
    · intro c _ hcb
      rw [conjTranspose_apply]
      rcases lt_or_gt_of_ne hcb with hlt | hgt
      · rw [hFz c hlt, zero_mul]
      · rw [hΔ c d hgt.le hd (fun h => hcb (Prod.ext_iff.1 h).1), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hrow a le_rfl, if_pos rfl, hF1, mul_one]
  · intro d _ hda
    rcases lt_or_gt_of_ne hda with hlt | hgt
    · rw [hF d a hlt, mul_zero]
    · rw [hrow d hgt.le, if_neg hda, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem cK_skew (c : WlocSk.NB.CI k r → ℂ) (s : Fin r → ℝ) (i j : Fin r) :
    star (WlocSk.NB.cK c s j i) = -WlocSk.NB.cK c s i j := by
  unfold WlocSk.NB.cK
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.2 h.le]
  · simp
  · simp [h, not_lt.2 h.le]

theorem skew_conj (F Δ : Matrix (Fin r) (Fin r) ℂ) (hΔ : ∀ i j, star (Δ j i) = -Δ i j) (b a : Fin r) :
    star ((Fᴴ * Δ * F) a b) = -(Fᴴ * Δ * F) b a := by
  have hD : Δᴴ = -Δ := by
    ext i j
    rw [conjTranspose_apply, hΔ, neg_apply]
  have hM : (Fᴴ * Δ * F)ᴴ = -(Fᴴ * Δ * F) := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hD]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  have h2 := congrArg (fun M => M b a) hM
  simp only [conjTranspose_apply, neg_apply] at h2
  exact h2

end Tri

section TriBk

variable {ι : Type} {r k : ℕ}

theorem chart_difference_formula (cx cy : WlocSk.NB.CI k r → ℂ) (sx : Fin r → ℝ) :
    WlocSk.NB.dlt (WlocSk.NB.phi0 cx sx) cy =
      (WlocSk.NB.cF cy)ᴴ * ((WlocSk.NB.cF cx)ᴴ * (WlocSk.NB.cB cx * WlocSk.NB.cE cy)) +
        (WlocSk.NB.cF cy)ᴴ * WlocSk.NB.cM cx sx * WlocSk.NB.cF cy := by
  unfold WlocSk.NB.dlt WlocSk.NB.phi0
  rw [WlocSk.NB.bF_mk, WlocSk.NB.bB_mk, WlocSk.NB.bC_mk]
  have e : (WlocSk.NB.cF cx)ᴴ * (WlocSk.NB.cC cx sx * WlocSk.NB.cF cy) = WlocSk.NB.cM cx sx * WlocSk.NB.cF cy := by
    unfold WlocSk.NB.cC
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, WlocSk.NB.cF_cA, Matrix.one_mul]
  rw [Matrix.mul_add (WlocSk.NB.cF cx)ᴴ, e, Matrix.mul_add, Matrix.mul_assoc (WlocSk.NB.cF cy)ᴴ]

theorem kcore0 (cx cx' cy cy' : WlocSk.NB.CI k r → ℂ) (sx sx' : Fin r → ℝ) (b a : Fin r)
    (hAx : WlocSk.NB.cA cx = WlocSk.NB.cA cx') (hBx : WlocSk.NB.cB cx = WlocSk.NB.cB cx')
    (hAy : WlocSk.NB.cA cy = WlocSk.NB.cA cy') (hBy : WlocSk.NB.cB cy = WlocSk.NB.cB cy')
    (hΔ : ∀ c d : Fin r, b ≤ c → a ≤ d → (c, d) ≠ (b, a) → WlocSk.NB.cK cx sx c d = WlocSk.NB.cK cx' sx' c d) :
    WlocSk.NB.dlt (WlocSk.NB.phi0 cx sx) cy = WlocSk.NB.dlt (WlocSk.NB.phi0 cx' sx') cy' +
        (WlocSk.NB.cF cy)ᴴ * (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') * WlocSk.NB.cF cy ∧
      ((WlocSk.NB.cF cy)ᴴ * (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') * WlocSk.NB.cF cy) b a =
        WlocSk.NB.cK cx sx b a - WlocSk.NB.cK cx' sx' b a ∧
      ∀ i j, star (((WlocSk.NB.cF cy)ᴴ * (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') * WlocSk.NB.cF cy) j i) =
        -((WlocSk.NB.cF cy)ᴴ * (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') * WlocSk.NB.cF cy) i j := by
  have hFx : WlocSk.NB.cF cx = WlocSk.NB.cF cx' := by unfold WlocSk.NB.cF; rw [hAx]
  have hFy : WlocSk.NB.cF cy = WlocSk.NB.cF cy' := by unfold WlocSk.NB.cF; rw [hAy]
  have hEx : WlocSk.NB.cE cx = WlocSk.NB.cE cx' := by unfold WlocSk.NB.cE; rw [hBx, hFx]
  have hEy : WlocSk.NB.cE cy = WlocSk.NB.cE cy' := by unfold WlocSk.NB.cE; rw [hBy, hFy]
  have hM : WlocSk.NB.cM cx sx = WlocSk.NB.cM cx' sx' + (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') := by
    unfold WlocSk.NB.cM; rw [hEx]; abel
  have hskew : ∀ i j, star ((WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') j i) =
      -(WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') i j := fun i j => by
    rw [Matrix.sub_apply, Matrix.sub_apply, star_sub, cK_skew, cK_skew, neg_sub_neg, neg_sub]
  have hmain : WlocSk.NB.dlt (WlocSk.NB.phi0 cx sx) cy = WlocSk.NB.dlt (WlocSk.NB.phi0 cx' sx') cy' +
      (WlocSk.NB.cF cy)ᴴ * (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') * WlocSk.NB.cF cy := by
    rw [chart_difference_formula, chart_difference_formula, hM, ← hFx, ← hBx, ← hFy, ← hEy, Matrix.mul_add, Matrix.add_mul, add_assoc]
  have htri : ((WlocSk.NB.cF cy)ᴴ * (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') * WlocSk.NB.cF cy) b a =
      WlocSk.NB.cK cx sx b a - WlocSk.NB.cK cx' sx' b a := by
    obtain ⟨hF0, hF1⟩ := cF_low (k := k) cy
    refine tri_conj _ _ hF0 hF1 b a fun c d hbc had hne => ?_
    rw [Matrix.sub_apply, sub_eq_zero]
    exact hΔ c d hbc had hne
  exact ⟨hmain, htri, fun i j => skew_conj (WlocSk.NB.cF cy) (WlocSk.NB.cK cx sx - WlocSk.NB.cK cx' sx') hskew i j⟩

theorem cK_agree (T : ℝ) (x x' : ∀ q : CBlk r, CSpc ι k q) (v : ι) (b a : Fin r)
    (hK : ∀ q : LsNc5.LtPair r, b.val + a.val < q.1.1.val + q.1.2.val → x (Sum.inr (Sum.inl q)) = x' (Sum.inr (Sum.inl q)))
    (hD : ∀ c : Fin r, b.val + a.val < 2 * c.val → x (Sum.inr (Sum.inr c)) = x' (Sum.inr (Sum.inr c)))
    (c d : Fin r) (hbc : b ≤ c) (had : a ≤ d) (hne : (c, d) ≠ (b, a)) :
    WlocSk.NB.cK (chAt T x v).1 (chAt T x v).2 c d = WlocSk.NB.cK (chAt T x' v).1 (chAt T x' v).2 c d := by
  have hlt : b.val + a.val < c.val + d.val := by
    have h1 : b.val ≤ c.val := hbc
    have h2 : a.val ≤ d.val := had
    by_contra hcon
    apply hne
    have e1 : c = b := Fin.ext (by omega)
    have e2 : d = a := Fin.ext (by omega)
    rw [e1, e2]
  simp only [WlocSk.NB.cK]
  split_ifs with h1 h2
  · exact congrFun (hK ⟨(c, d), h1⟩ hlt) v
  · show -star ((x (Sum.inr (Sum.inl ⟨(d, c), h2⟩)) : ι → ℂ) v) = -star ((x' (Sum.inr (Sum.inl ⟨(d, c), h2⟩)) : ι → ℂ) v)
    rw [hK ⟨(d, c), h2⟩ (by show b.val + a.val < d.val + c.val; omega)]
  · have hcd : c = d := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    subst hcd
    show (((x (Sum.inr (Sum.inr c)) : ι → ℝ) v : ℝ) : ℂ) * Complex.I = (((x' (Sum.inr (Sum.inr c)) : ι → ℝ) v : ℝ) : ℂ) * Complex.I
    rw [hD c (by omega)]

theorem cAB_agree (T : ℝ) (x x' : ∀ q : CBlk r, CSpc ι k q) (v : ι)
    (hX : ∀ q : LsNc5.LtPair r, x (Sum.inl (Sum.inl q)) = x' (Sum.inl (Sum.inl q)))
    (hR : ∀ c : Fin r, x (Sum.inl (Sum.inr c)) = x' (Sum.inl (Sum.inr c))) :
    WlocSk.NB.cA (chAt T x v).1 = WlocSk.NB.cA (chAt T x' v).1 ∧ WlocSk.NB.cB (chAt T x v).1 = WlocSk.NB.cB (chAt T x' v).1 := by
  refine ⟨?_, ?_⟩
  · funext i l
    simp only [WlocSk.NB.cA]
    split_ifs with h1 h2
    · exact congrFun (hX ⟨(i, l), h1⟩) v
    · rfl
    · rfl
  · funext i l
    show (x (Sum.inl (Sum.inr i)) : ι → Fin (k + 1) → ℂ) v l / sclT T l = (x' (Sum.inl (Sum.inr i)) : ι → Fin (k + 1) → ℂ) v l / sclT T l
    rw [hR i]

theorem bk_tri {T : ℝ} (hT : 0 < T) (p : CBlk r) (x x' y y' : ∀ q : CBlk r, CSpc ι k q)
    (hxy : ∀ q, cHgt q < cHgt p → x q = x' q ∧ y q = y' q) : Bk T p x y = Bk T p x' y' := by
  have ag : ∀ q, cHgt q < cHgt p → x q = x' q := fun q h => (hxy q h).1
  have ag' : ∀ q, cHgt q < cHgt p → y q = y' q := fun q h => (hxy q h).2
  rcases p with ((p | b) | (p | a))
  ·
    obtain ⟨⟨b, a⟩, hba⟩ := p
    funext v
    show WlocSk.NB.shG (ph0 (chAt T x v)) (chAt T y v).1 (Sum.inl ⟨(b, a), hba⟩) - x (Sum.inl (Sum.inl ⟨(b, a), hba⟩)) v =
      WlocSk.NB.shG (ph0 (chAt T x' v)) (chAt T y' v).1 (Sum.inl ⟨(b, a), hba⟩) - x' (Sum.inl (Sum.inl ⟨(b, a), hba⟩)) v
    simp only [WlocSk.NB.shG, ph0, WlocSk.NB.phi0, WlocSk.NB.bA_mk]
    rw [sub_eq_sub_iff_sub_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · simp only [if_pos hba, WlocSk.NB.cA, dif_pos hba, dif_neg (lt_irrefl a), if_pos rfl, ite_true, mul_one]
      rfl
    · intro c _ hca
      by_cases hbc : b < c
      · simp only [if_pos hbc]
        rcases lt_or_gt_of_ne hca with h | h
        · have e1 : x (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) = x' (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) :=
            ag _ (by show c.val - b.val < a.val - b.val; omega)
          have e2 : y (Sum.inl (Sum.inl ⟨(c, a), h⟩)) = y' (Sum.inl (Sum.inl ⟨(c, a), h⟩)) :=
            ag' _ (by show a.val - c.val < a.val - b.val; omega)
          simp only [WlocSk.NB.cA, dif_pos hbc, dif_pos h]
          show x (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) v * y (Sum.inl (Sum.inl ⟨(c, a), h⟩)) v -
            x' (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) v * y' (Sum.inl (Sum.inl ⟨(c, a), h⟩)) v = 0
          rw [e1, e2, sub_self]
        · simp only [WlocSk.NB.cA, dif_neg (not_lt.2 h.le), if_neg (ne_of_gt h), mul_zero, sub_self]
      · simp only [if_neg hbc, sub_self]
    · intro h; exact absurd (Finset.mem_univ a) h
  ·
    funext v j
    have hsc := sclT_ne hT (k := k) j
    have hS : ∀ xx yy : ∀ q : CBlk r, CSpc ι k q, Bk T (Sum.inl (Sum.inr b)) xx yy v j =
        sclT T j * ∑ c, (if b < c then WlocSk.NB.cA (chAt T xx v).1 b c * WlocSk.NB.cB (chAt T yy v).1 c j else 0) := by
      intro xx yy
      show sclT T j * WlocSk.NB.shG (ph0 (chAt T xx v)) (chAt T yy v).1 (Sum.inr (Sum.inl (b, j))) -
        xx (Sum.inl (Sum.inr b)) v j = _
      simp only [WlocSk.NB.shG, ph0, WlocSk.NB.phi0, WlocSk.NB.bA_mk, WlocSk.NB.bB_mk]
      have e : sclT T j * WlocSk.NB.cB (chAt T xx v).1 b j = xx (Sum.inl (Sum.inr b)) v j := by
        show sclT T j * (xx (Sum.inl (Sum.inr b)) v j / sclT T j) = _
        field_simp
      rw [mul_add, e, add_sub_cancel_right]
    rw [hS, hS]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hbc : b < c
    · have e1 : x (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) = x' (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) :=
        ag _ (by show c.val - b.val < r + (r - b.val); have := c.isLt; omega)
      have e2 : y (Sum.inl (Sum.inr c)) = y' (Sum.inl (Sum.inr c)) :=
        ag' _ (by show r + (r - c.val) < r + (r - b.val); have := c.isLt; omega)
      simp only [if_pos hbc, WlocSk.NB.cA, dif_pos hbc, WlocSk.NB.cB]
      show x (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) v * (y (Sum.inl (Sum.inr c)) v j / sclT T j) =
        x' (Sum.inl (Sum.inl ⟨(b, c), hbc⟩)) v * (y' (Sum.inl (Sum.inr c)) v j / sclT T j)
      rw [e1, e2]
    · simp only [if_neg hbc]
  ·
    obtain ⟨⟨b, a⟩, hba⟩ := p
    funext v
    have hX : ∀ q : LsNc5.LtPair r, x (Sum.inl (Sum.inl q)) = x' (Sum.inl (Sum.inl q)) ∧
        y (Sum.inl (Sum.inl q)) = y' (Sum.inl (Sum.inl q)) := fun q =>
      hxy _ (by show q.1.2.val - q.1.1.val < 2 * r + 1 + (2 * r - (b.val + a.val)); have := q.1.2.isLt; omega)
    have hR : ∀ c : Fin r, x (Sum.inl (Sum.inr c)) = x' (Sum.inl (Sum.inr c)) ∧
        y (Sum.inl (Sum.inr c)) = y' (Sum.inl (Sum.inr c)) := fun c =>
      hxy _ (by show r + (r - c.val) < 2 * r + 1 + (2 * r - (b.val + a.val)); omega)
    have hK : ∀ q : LsNc5.LtPair r, b.val + a.val < q.1.1.val + q.1.2.val →
        x (Sum.inr (Sum.inl q)) = x' (Sum.inr (Sum.inl q)) := fun q hq =>
      ag _ (by show 2 * r + 1 + (2 * r - (q.1.1.val + q.1.2.val)) < 2 * r + 1 + (2 * r - (b.val + a.val))
               have := q.1.1.isLt; have := q.1.2.isLt; omega)
    have hD : ∀ c : Fin r, b.val + a.val < 2 * c.val → x (Sum.inr (Sum.inr c)) = x' (Sum.inr (Sum.inr c)) :=
      fun c hc => ag _ (by show 2 * r + 1 + (2 * r - 2 * c.val) < 2 * r + 1 + (2 * r - (b.val + a.val))
                           have := c.isLt; omega)
    obtain ⟨hAx, hBx⟩ := cAB_agree T x x' v (fun q => (hX q).1) (fun c => (hR c).1)
    obtain ⟨hAy, hBy⟩ := cAB_agree T y y' v (fun q => (hX q).2) (fun c => (hR c).2)
    obtain ⟨h1, h2, h3⟩ := kcore0 _ _ _ _ _ _ b a hAx hBx hAy hBy (cK_agree T x x' v b a hK hD)
    show (WlocSk.NB.dlt (ph0 (chAt T x v)) (chAt T y v).1 b a - star (WlocSk.NB.dlt (ph0 (chAt T x v)) (chAt T y v).1 a b)) / 2 -
        x (Sum.inr (Sum.inl ⟨(b, a), hba⟩)) v =
      (WlocSk.NB.dlt (ph0 (chAt T x' v)) (chAt T y' v).1 b a - star (WlocSk.NB.dlt (ph0 (chAt T x' v)) (chAt T y' v).1 a b)) / 2 -
        x' (Sum.inr (Sum.inl ⟨(b, a), hba⟩)) v
    simp only [ph0] at *
    rw [h1, Matrix.add_apply, Matrix.add_apply, star_add, h3 b a, h2]
    have e1 : WlocSk.NB.cK (chAt T x v).1 (chAt T x v).2 b a = x (Sum.inr (Sum.inl ⟨(b, a), hba⟩)) v := by
      simp only [WlocSk.NB.cK, dif_pos hba]; rfl
    have e2 : WlocSk.NB.cK (chAt T x' v).1 (chAt T x' v).2 b a = x' (Sum.inr (Sum.inl ⟨(b, a), hba⟩)) v := by
      simp only [WlocSk.NB.cK, dif_pos hba]; rfl
    rw [e1, e2]
    ring
  ·
    funext v
    have hX : ∀ q : LsNc5.LtPair r, x (Sum.inl (Sum.inl q)) = x' (Sum.inl (Sum.inl q)) ∧
        y (Sum.inl (Sum.inl q)) = y' (Sum.inl (Sum.inl q)) := fun q =>
      hxy _ (by show q.1.2.val - q.1.1.val < 2 * r + 1 + (2 * r - 2 * a.val); have := q.1.2.isLt; omega)
    have hR : ∀ c : Fin r, x (Sum.inl (Sum.inr c)) = x' (Sum.inl (Sum.inr c)) ∧
        y (Sum.inl (Sum.inr c)) = y' (Sum.inl (Sum.inr c)) := fun c =>
      hxy _ (by show r + (r - c.val) < 2 * r + 1 + (2 * r - 2 * a.val); omega)
    have hK : ∀ q : LsNc5.LtPair r, a.val + a.val < q.1.1.val + q.1.2.val →
        x (Sum.inr (Sum.inl q)) = x' (Sum.inr (Sum.inl q)) := fun q hq =>
      ag _ (by show 2 * r + 1 + (2 * r - (q.1.1.val + q.1.2.val)) < 2 * r + 1 + (2 * r - 2 * a.val)
               have := q.1.1.isLt; have := q.1.2.isLt; omega)
    have hD : ∀ c : Fin r, a.val + a.val < 2 * c.val → x (Sum.inr (Sum.inr c)) = x' (Sum.inr (Sum.inr c)) :=
      fun c hc => ag _ (by show 2 * r + 1 + (2 * r - 2 * c.val) < 2 * r + 1 + (2 * r - 2 * a.val)
                           have := c.isLt; omega)
    obtain ⟨hAx, hBx⟩ := cAB_agree T x x' v (fun q => (hX q).1) (fun c => (hR c).1)
    obtain ⟨hAy, hBy⟩ := cAB_agree T y y' v (fun q => (hX q).2) (fun c => (hR c).2)
    obtain ⟨h1, h2, -⟩ := kcore0 _ _ _ _ _ _ a a hAx hBx hAy hBy (cK_agree T x x' v a a hK hD)
    show (WlocSk.NB.dlt (ph0 (chAt T x v)) (chAt T y v).1 a a).im - x (Sum.inr (Sum.inr a)) v =
      (WlocSk.NB.dlt (ph0 (chAt T x' v)) (chAt T y' v).1 a a).im - x' (Sum.inr (Sum.inr a)) v
    simp only [ph0] at *
    rw [h1, Matrix.add_apply, Complex.add_im, h2]
    simp only [WlocSk.NB.cK, lt_irrefl, dif_neg, not_false_eq_true, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    show _ + ((x (Sum.inr (Sum.inr a)) v) - (x' (Sum.inr (Sum.inr a)) v)) - x (Sum.inr (Sum.inr a)) v = _
    ring

end TriBk

section Assemble

theorem mOf_one {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) : mOf hn ε e f w (z0v T z) 1 = 1 := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  show Qi ε e f w (z0v T z) * uMat 1 * Qm e f w (z0v T z) = 1
  rw [uMat_one, Matrix.mul_one, Qi_mul_Qm hFJ]

theorem blkOf_one {ι : Type} {r k : ℕ} (T : ℝ) :
    blkOf (ι := ι) (r := r) (k := k) T (fun _ => 1) = 0 := by
  funext p
  rcases p with ((⟨⟨b, a⟩, hba⟩ | b) | (⟨⟨b, a⟩, hba⟩ | a))
  · funext v
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r b) (eI k r a) = 0
    rw [Matrix.one_apply, if_neg]
    intro h; exact (ne_of_lt hba) (by have := congrArg Fin.val h; simp [eI] at this; exact Fin.ext this)
  · funext v j
    show sclT T j * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r b) (wI k r j) = 0
    rw [Matrix.one_apply, if_neg, mul_zero]
    intro h; have := congrArg Fin.val h; simp [eI, wI] at this; omega
  · funext v
    show WlocSk.NB.kof 1 b a = 0
    have hm : WlocSk.NB.mof (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = 0 := by
      funext i l
      simp only [WlocSk.NB.mof, WlocSk.NB.bF, WlocSk.NB.bC, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      have hne : eI k r c ≠ esI k r l := by
        intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega
      rw [if_neg hne, mul_zero]
    simp [WlocSk.NB.kof, hm]
  · funext v
    show (WlocSk.NB.mof (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) a a).im = 0
    have hm : WlocSk.NB.mof (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) a a = 0 := by
      simp only [WlocSk.NB.mof, WlocSk.NB.bF, WlocSk.NB.bC, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      have hne : eI k r c ≠ esI k r a := by
        intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega
      rw [if_neg hne, mul_zero]
    rw [hm, Complex.zero_im]

variable {D : D7} (X : HidaSetting D)

def mX (u : D.what₂.Word) (s : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  mOf (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (z0v (Tw u) (ProductExactness.zV X u v)) (s v)

theorem blk_eq (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.NinfU u) :
    blk X u s = blkOf (Tw u) (mX X u s) := by
  have mX_facts : ∀ (u : D.what₂.Word) (v : InfinitePlace X.B.I.F), _ := fun u v => mOf_facts (nX X) (X.B.I.ε v) (eV X v)
    (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v)
    (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  funext p
  rcases p with ((⟨⟨b, a⟩, hba⟩ | b) | (⟨⟨b, a⟩, hba⟩ | a))
  · funext v
    exact (mX_facts u v).2.2.1 (s v) b a
  · funext v j
    obtain ⟨-, -, -, hw, hz, -⟩ := mX_facts u v
    show (if h : j.val < D.R.k then LsNc5.phiMat X u v s b ⟨j.val, h⟩ else LsNc5.yVec X u v s b) =
      sclT (Tw u) j * mX X u s v (eI D.R.k D.R.rS b) (wI D.R.k D.R.rS j)
    by_cases h : j.val < D.R.k
    · rw [dif_pos h, sclT, if_pos h, one_mul]
      have := hw (s v) b ⟨j.val, h⟩
      have e : Fin.castSucc (⟨j.val, h⟩ : Fin D.R.k) = j := Fin.ext rfl
      rw [e] at this
      exact this
    · rw [dif_neg h, sclT, if_neg h]
      have e : j = Fin.last D.R.k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst e
      exact hz (s v) b
  · funext v
    obtain ⟨-, -, -, -, -, hM⟩ := mX_facts u v
    show (LsNc5.mMat X v s b a - star (LsNc5.mMat X v s a b)) / 2 = WlocSk.NB.kof (mX X u s v) b a
    have e : LsNc5.mMat X v s = WlocSk.NB.mof (mX X u s v) := hM (s v) (hs v)
    rw [e]; rfl
  · funext v
    obtain ⟨-, -, -, -, -, hM⟩ := mX_facts u v
    show (LsNc5.mMat X v s a a).im = WlocSk.NB.psiR (mX X u s v) a
    have e : LsNc5.mMat X v s = WlocSk.NB.mof (mX X u s v) := hM (s v) (hs v)
    rw [e]; rfl

end Assemble

section Meas

variable {r k : ℕ}

theorem cont_dlt : Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
    WlocSk.NB.dlt mc.1 mc.2 := by
  have hent : ∀ i j : Fin (2 * r + k + 1), Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ×
      (WlocSk.NB.CI k r → ℂ) => mc.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hbB : Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.bB mc.1 := continuous_pi fun a => continuous_pi fun j => hent _ _
  have hbC : Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.bC mc.1 := continuous_pi fun a => continuous_pi fun j => hent _ _
  have hbF : Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.bF mc.1 := continuous_pi fun a => continuous_pi fun j => hent _ _
  have hcE := WlocSk.NB.continuous_cE.comp (continuous_snd (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (Y := WlocSk.NB.CI k r → ℂ))
  have hcF := WlocSk.NB.continuous_cF.comp (continuous_snd (X := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (Y := WlocSk.NB.CI k r → ℂ))
  unfold WlocSk.NB.dlt
  exact hcF.matrix_conjTranspose.matrix_mul (hbF.matrix_conjTranspose.matrix_mul
    ((hbB.matrix_mul hcE).add (hbC.matrix_mul hcF)))

theorem cont_shG (i : WlocSk.NB.CI k r) :
    Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.shG mc.1 mc.2 i := by
  have hent : ∀ i j : Fin (2 * r + k + 1), Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ×
      (WlocSk.NB.CI k r → ℂ) => mc.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hcA : ∀ a b, Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.cA mc.2 a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp (WlocSk.NB.continuous_cA.comp continuous_snd))
  have hcB : ∀ a j, Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.cB mc.2 a j := fun a j => (continuous_apply _).comp continuous_snd
  rcases i with p | q | p
  · show Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      ∑ c, if p.1.1 < c then WlocSk.NB.bA mc.1 p.1.1 c * WlocSk.NB.cA mc.2 c p.1.2 else 0
    refine continuous_finset_sum _ fun c _ => ?_
    by_cases h : p.1.1 < c
    · simp only [if_pos h]; exact (hent _ _).mul (hcA _ _)
    · simp only [if_neg h]; exact continuous_const
  · show Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      (∑ c, if q.1 < c then WlocSk.NB.bA mc.1 q.1 c * WlocSk.NB.cB mc.2 c q.2 else 0) + WlocSk.NB.bB mc.1 q.1 q.2
    refine (continuous_finset_sum _ fun c _ => ?_).add (hent _ _)
    by_cases h : q.1 < c
    · simp only [if_pos h]; exact (hent _ _).mul (hcB _ _)
    · simp only [if_neg h]; exact continuous_const
  · show Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      (WlocSk.NB.dlt mc.1 mc.2 p.1.1 p.1.2 - star (WlocSk.NB.dlt mc.1 mc.2 p.1.2 p.1.1)) / 2
    have h1 : ∀ a b : Fin r, Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ×
        (WlocSk.NB.CI k r → ℂ) => WlocSk.NB.dlt mc.1 mc.2 a b := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp cont_dlt)
    exact ((h1 _ _).sub (h1 _ _).star).div_const 2

theorem cont_shH (a : Fin r) :
    Continuous fun mc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ × (WlocSk.NB.CI k r → ℂ) =>
      WlocSk.NB.shH mc.1 mc.2 a :=
  Complex.continuous_im.comp ((continuous_apply a).comp ((continuous_apply a).comp cont_dlt))

variable {ι : Type}

theorem meas_chAt (T : ℝ) (v : ι) : Measurable (fun x : (∀ q : CBlk r, CSpc ι k q) => chAt T x v) := by
  refine Measurable.prodMk (measurable_pi_lambda _ fun c => ?_) (measurable_pi_lambda _ fun a => ?_)
  · rcases c with p | ⟨b, j⟩ | p
    · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inl (Sum.inl p) : CBlk r))
    · exact ((measurable_pi_apply j).comp ((measurable_pi_apply v).comp
        (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r)))).div_const _
    · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inr (Sum.inl p) : CBlk r))
  · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inr (Sum.inr a) : CBlk r))

set_option maxHeartbeats 800000 in
theorem meas_Bk (T : ℝ) (p : CBlk r) :
    Measurable (fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) => Bk T p z.1 z.2) := by
  haveI : SecondCountableTopology ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) := inferInstance
  haveI : OpensMeasurableSpace (((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))) :=
    inferInstance
  have hφ : Continuous fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
      ((WlocSk.NB.phi0 cc.1.1 cc.1.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), cc.2.1) :=
    (WlocSk.NB.continuous_nilpotent_chart.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)
  have hmc : ∀ v : ι, Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
      (chAt T z.1 v, chAt T z.2 v) := fun v =>
    ((meas_chAt T v).comp measurable_fst).prodMk ((meas_chAt T v).comp measurable_snd)
  have hG : ∀ (i : WlocSk.NB.CI k r) (v : ι), Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
      WlocSk.NB.shG (ph0 (chAt T z.1 v)) (chAt T z.2 v).1 i := fun i v => by
    have hc : Continuous fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
        WlocSk.NB.shG (ph0 cc.1) cc.2.1 i := (cont_shG i).comp hφ
    exact Measurable.comp (g := fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
        WlocSk.NB.shG (ph0 cc.1) cc.2.1 i) (f := fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
        (chAt T z.1 v, chAt T z.2 v)) hc.measurable (hmc v)
  have hH : ∀ (a : Fin r) (v : ι), Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
      WlocSk.NB.shH (ph0 (chAt T z.1 v)) (chAt T z.2 v).1 a := fun a v => by
    have hcM : Continuous fun t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) => WlocSk.NB.cM t.1 t.2 := by
      have hE := WlocSk.NB.continuous_cE.comp (continuous_fst (X := WlocSk.NB.CI k r → ℂ) (Y := Fin r → ℝ))
      exact WlocSk.NB.continuous_cK.sub
        (((hE.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hE).const_smul (1 / 2 : ℂ))
    have hd : Continuous fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
        WlocSk.NB.dlt (ph0 cc.1) cc.2.1 := by
      have e : (fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
          WlocSk.NB.dlt (ph0 cc.1) cc.2.1) = fun cc =>
          (WlocSk.NB.cF cc.2.1)ᴴ * ((WlocSk.NB.cF cc.1.1)ᴴ * (WlocSk.NB.cB cc.1.1 * WlocSk.NB.cE cc.2.1)) +
            (WlocSk.NB.cF cc.2.1)ᴴ * WlocSk.NB.cM cc.1.1 cc.1.2 * WlocSk.NB.cF cc.2.1 :=
        funext fun cc => chart_difference_formula cc.1.1 cc.2.1 cc.1.2
      rw [e]
      have hy : Continuous fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
          cc.2.1 := continuous_fst.comp continuous_snd
      have hx : Continuous fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
          cc.1.1 := continuous_fst.comp continuous_fst
      have hFy := WlocSk.NB.continuous_cF.comp' hy
      have hFx := WlocSk.NB.continuous_cF.comp' hx
      have hBx := WlocSk.NB.continuous_cB.comp' hx
      have hEy := WlocSk.NB.continuous_cE.comp' hy
      have hMx := hcM.comp' (continuous_fst (X := (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))
        (Y := (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)))
      exact (hFy.matrix_conjTranspose.matrix_mul (hFx.matrix_conjTranspose.matrix_mul (hBx.matrix_mul hEy))).add
        ((hFy.matrix_conjTranspose.matrix_mul hMx).matrix_mul hFy)
    have hc : Continuous fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
        WlocSk.NB.shH (ph0 cc.1) cc.2.1 a :=
      Complex.continuous_im.comp' (hd.matrix_elem a a)
    exact Measurable.comp (g := fun cc : ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) × ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) =>
        WlocSk.NB.shH (ph0 cc.1) cc.2.1 a) (f := fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
        (chAt T z.1 v, chAt T z.2 v)) hc.measurable (hmc v)
  rcases p with ((p | b) | (p | a))
  · refine measurable_pi_lambda _ fun v => ?_
    have h2 : Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
        (z.1 (Sum.inl (Sum.inl p)) : ι → ℂ) v :=
      (measurable_pi_apply v).comp ((measurable_pi_apply (Sum.inl (Sum.inl p) : CBlk r)).comp measurable_fst)
    exact (hG _ v).sub h2
  · refine measurable_pi_lambda _ fun v => measurable_pi_lambda _ fun j => ?_
    have h2 : Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
        (z.1 (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j :=
      (measurable_pi_apply j).comp ((measurable_pi_apply v).comp
        ((measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r)).comp measurable_fst))
    exact (measurable_const.mul (hG _ v)).sub h2
  · refine measurable_pi_lambda _ fun v => ?_
    have h2 : Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
        (z.1 (Sum.inr (Sum.inl p)) : ι → ℂ) v :=
      (measurable_pi_apply v).comp ((measurable_pi_apply (Sum.inr (Sum.inl p) : CBlk r)).comp measurable_fst)
    exact (hG _ v).sub h2
  · refine measurable_pi_lambda _ fun v => ?_
    have h2 : Measurable fun z : (∀ q : CBlk r, CSpc ι k q) × (∀ q : CBlk r, CSpc ι k q) =>
        (z.1 (Sum.inr (Sum.inr a)) : ι → ℝ) v :=
      (measurable_pi_apply v).comp ((measurable_pi_apply (Sum.inr (Sum.inr a) : CBlk r)).comp measurable_fst)
    exact (hH a v).sub h2

end Meas

theorem kapLaw_holds : KapLaw := by
  intro D X u
  have hT := ProductExactness.Tw_pos (D := D) u
  have hco : X.NinfU u = (ProductExactness.NinfG X u : Set X.B.I.Ginf) := (ProductExactness.NinfG_coe X u).symm
  have hmulN : ∀ s ∈ X.NinfU u, ∀ s' ∈ X.NinfU u, s * s' ∈ X.NinfU u := by
    intro s hs s' hs'; rw [hco] at hs hs' ⊢; exact (ProductExactness.NinfG X u).mul_mem hs hs'
  have hone : (1 : X.B.I.Ginf) ∈ X.NinfU u := by rw [hco]; exact (ProductExactness.NinfG X u).one_mem
  have mX_facts : ∀ v : InfinitePlace X.B.I.F, _ := fun v => mOf_facts (nX X) (X.B.I.ε v) (eV X v)
    (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v)
    (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  have hlaw : ∀ s ∈ X.NinfU u, ∀ s' ∈ X.NinfU u,
      blk X u (s * s') = Formalism.L2.SG.NGCut.SplitEmbedding.mlaw (Bk (Tw u)) (blk X u s) (blk X u s') := by
    intro s hs s' hs'
    rw [blk_eq X u _ (hmulN s hs s' hs'), blk_eq X u s hs, blk_eq X u s' hs']
    have e : mX X u (s * s') = fun v => mX X u s v * mX X u s' v :=
      funext fun v => (mX_facts v).1 (s v) (s' v)
    rw [e]
    exact law_blkOf hT _ _ (fun v => (mX_facts v).2.1 (s v) (hs v)) (fun v => (mX_facts v).2.1 (s' v) (hs' v))
  refine ⟨Bk (Tw u), meas_Bk (Tw u), fun p x x' y y' h => bk_tri hT p x x' y y' h, fun p x => ?_, hlaw⟩
  obtain ⟨σ, -, hσ⟩ := kapSurj_holds X u
  obtain ⟨hσN, hσb⟩ := hσ x
  have h1 := hlaw (σ x) hσN 1 hone
  rw [mul_one, hσb] at h1
  have h0 : blk X u 1 = 0 := by
    rw [blk_eq X u 1 hone]
    have e : mX X u 1 = fun _ => 1 := funext fun v => mOf_one (nX X) (X.B.I.ε v) (eV X v)
      (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v)
      (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
    rw [e]
    exact blkOf_one _
  rw [h0] at h1
  have h2 := congrFun h1 p
  simp only [Formalism.L2.SG.NGCut.SplitEmbedding.mlaw, Pi.zero_apply, add_zero] at h2
  calc Bk (Tw u) p x 0 = (x p + Bk (Tw u) p x 0) - x p := by abel
    _ = x p - x p := by rw [← h2]
    _ = 0 := sub_self _

end Formalism.L2.SG.Pf.NcReal.JX
