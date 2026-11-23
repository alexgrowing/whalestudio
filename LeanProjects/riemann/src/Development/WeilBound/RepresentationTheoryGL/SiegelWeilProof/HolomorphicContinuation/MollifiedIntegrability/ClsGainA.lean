import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainSt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem herm_star (y : E n) (i j : Fin n) : star (herm y i j) = herm y j i := by
  simpa [conjTranspose_apply] using congrFun (congrFun (herm_isHermitian y).eq j) i

theorem sq_smul (s : ℂ) (hs : s = 1 ∨ s = -1) (b : Matrix (Fin n) (Fin n) ℂ) :
    (1 - (Complex.I * s) • b) * (1 + (Complex.I * s) • b) = 1 + b * b := by
  have hc : (Complex.I * s) * (Complex.I * s) = -1 := by
    rcases hs with rfl | rfl <;> ring_nf <;> simp [Complex.I_sq]
  rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hc]
  simp only [neg_smul, one_smul]
  abel

theorem conjT_X (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (1 - (Complex.I * s) • herm y)ᴴ = 1 + (Complex.I * s) • herm y := by
  have hst : star (Complex.I * s) = -(Complex.I * s) := by
    rcases hs with rfl | rfl <;> simp [Complex.conj_I]
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hst, herm_isHermitian y, neg_smul, sub_neg_eq_add]

theorem smul_mulVec' (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem det_X_ne (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (1 - (Complex.I * s) • herm y).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hXv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  set q : ℂ := star v ⬝ᵥ (herm y *ᵥ v) with hq
  have hqr : star q = q := by
    rw [hq]
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, herm_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hqim : q.im = 0 := Complex.conj_eq_iff_im.1 hqr
  have hv2 : v = (Complex.I * s) • (herm y *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec'] at hXv
    exact sub_eq_zero.1 hXv
  have key : star v ⬝ᵥ v = (Complex.I * s) * q := by
    rw [hq, ← smul_eq_mul, ← dotProduct_smul, ← hv2]
  have hre : (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.normSq_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : 0 < (star v ⬝ᵥ v).re := by
    rw [hre]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have h0' : (star v ⬝ᵥ v).re = 0 := by
    rw [key]
    rcases hs with rfl | rfl <;> simp [Complex.mul_re, hqim]
  linarith

theorem det_Y_ne (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (1 + (Complex.I * s) • herm y).det ≠ 0 := by
  rw [← conjT_X s hs y, det_conjTranspose]
  exact (star_ne_zero).2 (det_X_ne s hs y)

theorem det_one_add_sq (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (1 + herm y * herm y).det = ((Complex.normSq (1 - (Complex.I * s) • herm y).det : ℝ) : ℂ) := by
  rw [← sq_smul s hs, det_mul, ← conjT_X s hs y, det_conjTranspose, Complex.star_def, Complex.mul_conj]

theorem dP_eq (y : E n) : (1 + herm y * herm y).det = ((dP y : ℝ) : ℂ) := by
  unfold dP
  rw [det_one_add_sq 1 (Or.inl rfl) y, Complex.ofReal_re]

theorem dP_pos (y : E n) : 0 < dP y := by
  have h := dP_eq y
  rw [det_one_add_sq 1 (Or.inl rfl) y] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.ofReal_re] at h2
  rw [← h2]
  exact Complex.normSq_pos.2 (det_X_ne 1 (Or.inl rfl) y)

theorem continuous_of' : Continuous fun B : MC n => Matrix.of B :=
  continuous_matrix fun i j => continuous_apply_apply i j

theorem isOpen_OmS (s : ℂ) : IsOpen (OmS (n := n) s) := by
  have g1 : Continuous fun B : MC n => 1 - (Complex.I * s) • Matrix.of B :=
    continuous_matrix fun i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      exact continuous_const.sub (continuous_const.mul (continuous_apply_apply i j))
  have g2 : Continuous fun B : MC n => 1 + (Complex.I * s) • Matrix.of B :=
    continuous_matrix fun i j => by
      simp only [Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      exact continuous_const.add (continuous_const.mul (continuous_apply_apply i j))
  have g3 : Continuous fun B : MC n => 1 + Matrix.of B * Matrix.of B :=
    continuous_const.add (continuous_of'.mul continuous_of')
  have h1 : Continuous fun B : MC n => (1 - (Complex.I * s) • Matrix.of B).det := g1.matrix_det
  have h2 : Continuous fun B : MC n => (1 + (Complex.I * s) • Matrix.of B).det := g2.matrix_det
  have h3 : Continuous fun B : MC n => (1 + Matrix.of B * Matrix.of B).det := g3.matrix_det
  have e : OmS (n := n) s = {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0} ∩
      ({B | (1 + (Complex.I * s) • Matrix.of B).det ≠ 0} ∩
        (fun B : MC n => (1 + Matrix.of B * Matrix.of B).det) ⁻¹' Complex.slitPlane) := rfl
  rw [e]
  exact (isOpen_ne_fun h1 continuous_const).inter ((isOpen_ne_fun h2 continuous_const).inter
    (Complex.isOpen_slitPlane.preimage h3))

theorem herm_mem_OmS (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (herm y : MC n) ∈ OmS s := by
  refine ⟨det_X_ne s hs y, det_Y_ne s hs y, ?_⟩
  show (1 + herm y * herm y).det ∈ Complex.slitPlane
  rw [dP_eq]
  exact Complex.ofReal_mem_slitPlane.2 (dP_pos y)

def EntAn (M : MC n → Matrix (Fin n) (Fin n) ℂ) (B₀ : MC n) : Prop := ∀ i j, AnalyticAt ℂ (fun B => M B i j) B₀

theorem an_entry (i j : Fin n) (B₀ : MC n) : AnalyticAt ℂ (fun B : MC n => B i j) B₀ := by
  have := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) i)).analyticAt B₀
  exact this

theorem an_det {M : MC n → Matrix (Fin n) (Fin n) ℂ} {B₀ : MC n} (h : EntAn M B₀) :
    AnalyticAt ℂ (fun B => (M B).det) B₀ := by
  have e : (fun B => (M B).det) =
      ∑ σ : Equiv.Perm (Fin n), fun B => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M B (σ i) i := by
    funext B
    rw [det_apply', Finset.sum_apply]
  rw [e]
  refine Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_
  have e2 : (fun B => ∏ i, M B (σ i) i) = ∏ i, fun B => M B (σ i) i := by
    funext B
    rw [Finset.prod_apply]
  rw [e2]
  exact Finset.analyticAt_prod _ fun i _ => h (σ i) i

theorem entAn_inv {M : MC n → Matrix (Fin n) (Fin n) ℂ} {B₀ : MC n} (h : EntAn M B₀) (h0 : (M B₀).det ≠ 0) :
    EntAn (fun B => (M B)⁻¹) B₀ := by
  intro i j
  have e : (fun B => (M B)⁻¹ i j) = fun B => ((M B).det)⁻¹ * ((M B).updateRow j (Pi.single i 1)).det := by
    funext B
    rw [inv_def, Matrix.smul_apply, adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [e]
  refine ((an_det h).inv h0).mul (an_det fun a b => ?_)
  simp only [updateRow_apply]
  by_cases hab : a = j
  · simp only [hab, if_true]
    exact analyticAt_const
  · simp only [hab, if_false]
    exact h a b

theorem entAn_X (c : ℂ) (B₀ : MC n) : EntAn (fun B : MC n => 1 - c • Matrix.of B) B₀ := fun i j => by
  simp only [Matrix.sub_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
  exact analyticAt_const.sub (analyticAt_const.mul (an_entry i j B₀))

theorem entAn_Y (c : ℂ) (B₀ : MC n) : EntAn (fun B : MC n => 1 + c • Matrix.of B) B₀ := fun i j => by
  simp only [Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
  exact analyticAt_const.add (analyticAt_const.mul (an_entry i j B₀))

theorem entAn_sq (B₀ : MC n) : EntAn (fun B : MC n => 1 + Matrix.of B * Matrix.of B) B₀ := fun i j => by
  simp only [Matrix.add_apply, Matrix.mul_apply, of_apply]
  refine analyticAt_const.add ?_
  have e : (fun B : MC n => ∑ k, B i k * B k j) = ∑ k, fun B : MC n => B i k * B k j := by
    funext B
    rw [Finset.sum_apply]
  rw [e]
  exact Finset.analyticAt_sum _ fun k _ => (an_entry i k B₀).mul (an_entry k j B₀)

theorem an_eval {ι : Type} (f : ι → MC n → ℂ) (B₀ : MC n) (hf : ∀ k, AnalyticAt ℂ (f k) B₀)
    (R : MvPolynomial ι ℂ) : AnalyticAt ℂ (fun B => MvPolynomial.eval (fun k => f k B) R) B₀ := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (hf k)

theorem an_clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B₀ : MC n) (hB : B₀ ∈ OmS s) :
    AnalyticAt ℂ (clsC s z p q R) B₀ := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hu := entAn_inv (entAn_X (Complex.I * s) B₀) h1
  have hv := entAn_inv (entAn_Y (Complex.I * s) B₀) h2
  have hexp : AnalyticAt ℂ (fun B : MC n => Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det)) B₀ :=
    (analyticAt_const.mul ((an_det (entAn_sq B₀)).clog h3)).cexp'
  have hdu : AnalyticAt ℂ (fun B : MC n => ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p) B₀ := (an_det hu).pow p
  have hdv : AnalyticAt ℂ (fun B : MC n => ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q) B₀ := (an_det hv).pow q
  have hf : ∀ k : Bool × Fin n × Fin n, AnalyticAt ℂ (fun B : MC n => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) B₀ := by
    rintro ⟨_ | _, a, b⟩
    · simp only [Bool.false_eq_true, if_false]
      exact hu a b
    · simp only [if_true]
      exact hv a b
  have hev := an_eval (fun k B => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) B₀ hf R
  unfold clsC
  exact ((hexp.mul hdu).mul hdv).mul hev

theorem clsC_herm (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    clsC s z p q R (herm y) = cls s z p q R y := by
  unfold clsC cls uM vM evUV
  have e : (1 + Matrix.of (herm y : MC n) * Matrix.of (herm y : MC n)).det = ((dP y : ℝ) : ℂ) := dP_eq y
  rw [e, Complex.cpow_def_of_ne_zero (by exact_mod_cast (dP_pos y).ne'), mul_comm (Complex.log _) (-z)]
  rfl

theorem ext : Ext := by
  intro n s hs
  refine ⟨isOpen_OmS s, herm_mem_OmS s hs, fun z p q R => ⟨fun B hB => an_clsC s z p q R B hB, clsC_herm s z p q R⟩⟩

def hermL : E n →L[ℝ] MC n := LinearMap.toContinuousLinearMap
  { toFun := fun y => (herm y : MC n)
    map_add' := fun x y => by
      funext i j
      show herm (x + y) i j = herm x i j + herm y i j
      simp only [herm, Pi.add_apply]
      push_cast
      ring
    map_smul' := fun c x => by
      funext i j
      show herm (c • x) i j = c • herm x i j
      simp only [herm, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring }

theorem hermL_apply (y : E n) : hermL y = (herm y : MC n) := rfl

theorem dirC_comp (G : MC n → ℂ) (y : E n) (hG : DifferentiableAt ℂ G (herm y)) (w : Fin n → Fin n → ℂ) :
    dirC (fun y => G (herm y)) w y =
      fderiv ℂ G (herm y) (hermL (fun a b => (w a b).re) + Complex.I • hermL (fun a b => (w a b).im)) := by
  have hd : HasFDerivAt (fun y => G (hermL y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp hermL) y :=
    (hG.hasFDerivAt.restrictScalars ℝ).comp y hermL.hasFDerivAt
  unfold dirC
  rw [show (fun y => G (herm y)) = fun y => G (hermL y) from rfl, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', map_add, map_smul,
    smul_eq_mul]

theorem hermC_eq (w : Fin n → Fin n → ℂ) :
    hermL (fun a b => (w a b).re) + Complex.I • hermL (fun a b => (w a b).im) =
      fun i j => (w i j + w j i) / 2 + Complex.I * (w i j - w j i) / 2 := by
  funext i j
  rw [hermL_apply, hermL_apply]
  show herm (fun a b => (w a b).re) i j + Complex.I * herm (fun a b => (w a b).im) i j = _
  simp only [herm]
  apply Complex.ext <;> simp <;> ring

theorem herm_vkl (k l : Fin n) :
    hermL (fun a b => (vkl k l a b).re) + Complex.I • hermL (fun a b => (vkl k l a b).im) = eU l k := by
  rw [hermC_eq]
  funext i j
  have c1 : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have c2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [vkl, eU, c1, c2]
  split_ifs <;>
    first
    | linear_combination (1 / 2 : ℂ) * Complex.I_sq
    | linear_combination (-1 / 2 : ℂ) * Complex.I_sq
    | ring1

theorem foldr_fderiv_eq (G : MC n → ℂ) (U : Set (MC n)) (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) :
    ∀ (m : ℕ) (v : Fin m → MC n),
      AnalyticOnNhd ℂ ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G) U ∧
      ∀ B ∈ U, ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G) B = iteratedFDeriv ℂ m G B v := by
  intro m
  induction m with
  | zero =>
    intro v
    refine ⟨by simpa [List.finRange_zero] using hG, fun B _ => ?_⟩
    simp [List.finRange_zero, iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro v
    obtain ⟨ha, he⟩ := ih (Fin.tail v)
    have e : (List.finRange (m + 1)).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G =
        fun B => fderiv ℂ ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (Fin.tail v k)) G) B (v 0) := by
      rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
      rfl
    rw [e]
    refine ⟨fun B hB => ((ContinuousLinearMap.apply ℂ ℂ (v 0)).analyticAt _).comp ((ha.fderiv_of_isOpen hU) B hB),
      fun B hB => ?_⟩
    have hev : (List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (Fin.tail v k)) G =ᶠ[nhds B]
        fun B => iteratedFDeriv ℂ m G B (Fin.tail v) :=
      Filter.eventually_of_mem (hU.mem_nhds hB) fun B' hB' => he B' hB'
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ m G) B :=
      ((hG.iteratedFDeriv_of_isOpen hU m) B hB).differentiableAt
    beta_reduce
    rw [hev.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]

theorem foldr_Dkl (σ : Equiv.Perm (Fin n)) (U : Set (MC n)) (hU : IsOpen U) (hherm : ∀ y : E n, (herm y : MC n) ∈ U)
    (G : MC n → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    ∀ L : List (Fin n), AnalyticOnNhd ℂ (L.foldr (fun k H => fun B => fderiv ℂ H B (eU (σ k) k)) G) U ∧
      L.foldr (fun k g => Dkl k (σ k) g) (fun y => G (herm y)) =
        fun y => (L.foldr (fun k H => fun B => fderiv ℂ H B (eU (σ k) k)) G) (herm y) := by
  intro L
  induction L with
  | nil => exact ⟨hG, rfl⟩
  | cons k L ih =>
    obtain ⟨ha, he⟩ := ih
    refine ⟨fun B hB => ((ContinuousLinearMap.apply ℂ ℂ (eU (σ k) k)).analyticAt _).comp
      ((ha.fderiv_of_isOpen hU) B hB), ?_⟩
    simp only [List.foldr_cons]
    rw [he]
    funext y
    unfold Dkl
    rw [dirC_comp _ y ((ha _ (hherm y)).differentiableAt), herm_vkl]

theorem delta_comp (U : Set (MC n)) (hU : IsOpen U) (hherm : ∀ y : E n, (herm y : MC n) ∈ U) (G : MC n → ℂ)
    (hG : AnalyticOnNhd ℂ G U) : Delta (fun y => G (herm y)) = fun y => cay G (herm y) := by
  funext y
  unfold Delta cay
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := congrFun (foldr_Dkl σ U hU hherm G hG (List.finRange n)).2 y
  have h2 := (foldr_fderiv_eq G U hU hG n (fun k => eU (σ k) k)).2 _ (hherm y)
  rw [Pi.smul_apply, h1, h2, smul_eq_mul]

theorem an_cay (U : Set (MC n)) (hU : IsOpen U) (G : MC n → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (cay G) U := by
  intro B hB
  have e : cay G = ∑ σ : Equiv.Perm (Fin n),
      fun B => ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n G B (fun k => eU (σ k) k) := by
    funext B
    unfold cay
    rw [Finset.sum_apply]
  rw [e]
  exact Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul
    (((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => MC n) ℂ (fun k => eU (σ k) k)).analyticAt _).comp
      ((hG.iteratedFDeriv_of_isOpen hU n) B hB))

theorem chain : Chain := by
  intro n U F hU hherm hF N
  induction N generalizing F with
  | zero => intro y; rfl
  | succ N ih =>
    intro y
    rw [Function.iterate_succ_apply, delta_comp U hU hherm F hF, ih (cay F) (an_cay U hU F hF) y,
      ← Function.iterate_succ_apply]

end PositivityTheory.Rg.Sw.WR.Z
