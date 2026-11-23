import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseBlock
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC

open Matrix NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexOrder

namespace GlobalTheory.PointOfFrames

theorem exists_block {r : ℕ} (q : ℕ) (K : Matrix (Fin r) (Fin r) ℂ) (hK : K.det ≠ 0)
    (h0 : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0) :
    ∃ m : Matrix (Fin r) (Fin r) ℂ, m.det ≠ 0 ∧ (∀ a c : Fin r, (a : ℕ) < q → m c a = K a c) ∧
      ∀ a c : Fin r, ¬ (a : ℕ) < q → m⁻¹ a c = K a c := by
  let K₁ : Matrix (Fin r) (Fin r) ℂ := of fun a c => if (a : ℕ) < q then K a c else (1 : Matrix _ _ ℂ) a c
  let K₂ : Matrix (Fin r) (Fin r) ℂ := of fun a c => if (a : ℕ) < q then (1 : Matrix _ _ ℂ) a c else K a c
  have hm : K₁ * K₂ = K := by
    ext a c
    rw [mul_apply]
    by_cases ha : (a : ℕ) < q
    · have : ∀ b, K₁ a b * K₂ b c = K a b * (1 : Matrix _ _ ℂ) b c := fun b => by
        by_cases hb : (b : ℕ) < q
        · simp only [K₁, K₂, of_apply, if_pos ha, if_pos hb]
        · simp only [K₁, K₂, of_apply, if_pos ha, h0 a b (by simp [ha, hb]), zero_mul]
      simp only [this]
      rw [← mul_apply, Matrix.mul_one]
    · have : ∀ b, K₁ a b * K₂ b c = (1 : Matrix _ _ ℂ) a b * K₂ b c := fun b => by
        simp only [K₁, of_apply, if_neg ha]
      simp only [this]
      rw [← mul_apply, Matrix.one_mul]
      simp only [K₂, of_apply, if_neg ha]
  rw [← hm, det_mul] at hK
  have u1 : IsUnit K₁ᵀ.det := by rw [det_transpose]; exact (left_ne_zero_of_mul hK).isUnit
  have u2 : IsUnit K₂.det := (right_ne_zero_of_mul hK).isUnit
  refine ⟨K₁ᵀ * K₂⁻¹, ?_, fun a c ha => ?_, fun a c ha => ?_⟩
  · rw [det_mul]
    exact (u1.mul (isUnit_nonsing_inv_det _ u2)).ne_zero
  · have e1 : K₂ *ᵥ Pi.single a 1 = Pi.single a 1 := by
      ext b
      by_cases hb : (b : ℕ) < q
      · simp [K₂, hb, one_apply, Pi.single_apply]
      · have : b ≠ a := fun h => hb (h ▸ ha)
        simp [K₂, hb, h0 b a (by simp [ha, hb]), this]
    have e2 : K₂⁻¹ *ᵥ Pi.single a 1 = Pi.single a 1 := by
      conv_lhs => rw [← e1]
      rw [mulVec_mulVec, nonsing_inv_mul _ u2, one_mulVec]
    have e3 := congrFun (congrArg (K₁ᵀ *ᵥ ·) e2) c
    simp only [mulVec_mulVec] at e3
    simpa [K₁, ha] using e3
  · have e1 : K a ᵥ* K₁ᵀ = K a := by
      rw [vecMul_transpose]
      ext b
      by_cases hb : (b : ℕ) < q
      · rw [h0 a b (by simp [ha, hb]), mulVec, dotProduct]
        refine Finset.sum_eq_zero fun d _ => ?_
        by_cases hd : (d : ℕ) < q
        · rw [h0 a d (by simp [ha, hd]), mul_zero]
        · simp only [K₁, of_apply, if_pos hb, h0 b d (by simp [hb, hd]), zero_mul]
      · simp [K₁, mulVec, dotProduct, hb, one_apply]
    have e2 : K a ᵥ* K₁ᵀ⁻¹ = K a := by
      conv_lhs => rw [← e1]
      rw [vecMul_vecMul, mul_nonsing_inv _ u1, vecMul_one]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ u2, ← congrFun e2 c, mul_apply, vecMul, dotProduct]
    simp only [K₂, of_apply, if_neg ha]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem rmul_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (b : Frame X.Ψ r)
    (hb : ∀ τ, (mat b τ).det ≠ 0) (h0 : ∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) :
    rmul x b ∈ X.dom := by
  refine AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [det_mul]; exact mul_ne_zero (hx τ).1 (hb τ)
  set f := Fin.castLE X.p0_le with hf
  have hs : ∀ (c : Fin X.p0) (g : Fin r → ℂ), ∑ a, b τ a (f c) * g a = ∑ a, b τ (f a) (f c) * g (f a) := by
    intro c g
    refine (Fintype.sum_of_injective f (Fin.castLE_injective _) _ _ (fun a ha => ?_) fun _ => rfl).symm
    rw [h0 τ a (f c) c.2 (fun h => ha ⟨⟨a, h⟩, rfl⟩), zero_mul]
  let B : Matrix (Fin X.p0) (Fin X.p0) ℂ := of fun c a => b τ (f a) (f c)
  have hc : ∀ c, FD.col (mat (rmul x b) τ) (f c) = ∑ a, B c a • FD.col (mat x τ) (f a) := by
    intro c
    ext i
    show (mat x τ * mat b τ) i (f c) = _
    rw [mul_apply, Finset.sum_apply]
    simp only [mul_comm (mat x τ i _)]
    exact hs c _
  have e : X.gramPos (rmul x b) τ = B * X.gramPos x τ * Bᴴ := by
    ext c d
    show hermC τ.1 X.Gm (FD.col (mat (rmul x b) τ) (f c)) (FD.col (mat (rmul x b) τ) (f d)) = _
    rw [hc, hc, hermC_sum_right, mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_right, hermC_sum_left, mul_apply, mul_comm]
    simp only [hermC_smul_left]
    rfl
  rw [e]
  refine (X.gramPos_posDef hx τ).mul_mul_conjTranspose_same ?_
  intro v w hvw
  have hl := (linearIndependent_cols_of_det_ne_zero (hb τ)).comp f (Fin.castLE_injective _)
  refine hl.fintypeLinearCombination_injective ?_
  ext a
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ha : (a : ℕ) < X.p0
  · exact congrFun hvw ⟨a, ha⟩
  · have : ∀ c, mat b τ a (f c) = 0 := fun c => h0 τ a (f c) c.2 ha
    simp [this]

open GlobalTheory.TrueCx in

theorem domPt_rmul_block (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type} (ι : Tau → X.Ψ) (x b : Frame X.Ψ r)
    (hb : ∀ τ, (mat b τ).det ≠ 0) (h0 : ∀ τ (a c : Fin r), (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b τ a c = 0) :
    domPt X hj ι (rmul x b) = domPt X hj ι x := by
  funext t
  set B := reindex (idx hj) (idx hj) (mat b (ι t)) with hB
  have h12 : B.toBlocks₁₂ = 0 := by
    ext a c
    refine h0 _ _ _ ?_ ?_
    · rw [idx_symm_inr]; exact c.2
    · rw [idx_symm_inl]; omega
  have hd : B.det ≠ 0 := by rw [hB, det_reindex_self]; exact hb _
  rw [← fromBlocks_toBlocks B, h12, det_fromBlocks_zero₁₂] at hd
  have e : frameCo X hj (rmul x b) (ι t) = frameCo X hj x (ι t) * B := by
    simp only [frameCo, hB, reindex_apply, submatrix_mul_equiv, Matrix.mul_assoc]
    rfl
  have h : (frameCo X hj (rmul x b) (ι t)).toBlocks₁₂ = (frameCo X hj x (ι t)).toBlocks₁₂ * B.toBlocks₂₂ ∧
      (frameCo X hj (rmul x b) (ι t)).toBlocks₂₂ = (frameCo X hj x (ι t)).toBlocks₂₂ * B.toBlocks₂₂ := by
    constructor <;>
    · rw [e]
      conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x (ι t)), ← fromBlocks_toBlocks B, h12, fromBlocks_multiply]
      simp
  simp only [domPt, moeb_zero]
  rw [h.1, h.2, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
    mul_nonsing_inv_cancel_right _ _ (right_ne_zero_of_mul hd).isUnit]

theorem exists_frame_mulVec (X : Data E r) {p : ℕ} (hr : r = p + X.p0) (ρ : (E →+* ℂ) → (E →+* ℂ))
    (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ) (hp : ∀ τ, ρ τ ∈ X.Ψ → m τ = p)
    (hq : ∀ τ, ρ τ ∉ X.Ψ → m τ = X.p0) {g : ℕ} (e : Fin g ≃ Σ τ, Fin (m τ)) (V : Matrix (Fin g) (Fin g) ℂ)
    (hV : IsUnit V.det) (hVt : ∀ j j', V j j' ≠ 0 → (e j).1 = (e j').1) (x : Frame X.Ψ r) :
    ∃ b : Frame X.Ψ r, (∀ τ, (mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
      ∀ v j, perFr X (rmul x b) v (ρ (e j).1) (e j).2 = (V *ᵥ fun j => perFr X x v (ρ (e j).1) (e j).2) j := by
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType p X.p0 r hr ρ hρ m hp hq
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (ρ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = ρ (e j).1 ∧ ((idx j).2 : ℕ) = X.p0 + (e j).2) ∨
      (ρ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (ρ (e j).1) ∧
        ((idx j).2 : ℕ) = X.p0 - 1 - (e j).2 ∧ ((e j).2 : ℕ) < X.p0) := ⟨e.trans f, fun j => hf (e j)⟩
  have hfr : ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (ρ (e j).1) (e j).2 =
      if ((idx j).2 : ℕ) < X.p0 then hermC (idx j).1.1 X.Gm (FD.col (mat x (idx j).1) (idx j).2)
        (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
    intro x v j
    have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (ρ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl
  have hbl : ∀ j j', V j j' ≠ 0 → (idx j).1 = (idx j').1 ∧ (((idx j).2 : ℕ) < X.p0 ↔ ((idx j').2 : ℕ) < X.p0) := by
    intro j j' h
    have h1 := congrArg ρ (hVt j j' h)
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · exact ⟨Subtype.ext (by rw [b1, b2, h1]), by omega⟩
    · exact absurd (h1 ▸ a1) a2
    · exact absurd (h1 ▸ a2) a1
    · exact ⟨Subtype.ext (by rw [b1, b2, h1]), by omega⟩
  let K : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => of fun a c => V (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < X.p0 ↔ (c : ℕ) < X.p0) → K τ a c = 0 := by
    intro τ a c hac
    by_contra h
    exact hac (by simpa using (hbl _ _ h).2)
  have hK : ∀ (w : Fin g → ℂ) τ a, (V *ᵥ w) (idx.symm (τ, a)) = (K τ *ᵥ fun c => w (idx.symm (τ, c))) a := by
    intro w τ a
    rw [mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · rfl
    · refine fun τ' _ hτ => Finset.sum_eq_zero fun c _ => mul_eq_zero_of_left ?_ _
      by_contra h
      exact hτ (by simpa using (hbl _ _ h).1.symm)
    · simp
  have hKd : ∀ τ, (K τ).det ≠ 0 := by
    intro τ h
    obtain ⟨v, hv, hv0⟩ := exists_mulVec_eq_zero_iff.2 h
    have : (fun j => if (idx j).1 = τ then v (idx j).2 else 0) = 0 := by
      refine eq_zero_of_mulVec_eq_zero hV.ne_zero (funext fun j => ?_)
      obtain ⟨⟨τ', a⟩, rfl⟩ := idx.symm.surjective j
      rw [hK]
      by_cases hτ : τ' = τ
      · subst hτ; simpa using congrFun hv0 a
      · simp [hτ, mulVec, dotProduct]
    exact hv (funext fun a => by simpa using congrFun this (idx.symm (τ, a)))
  choose b hb hb1 hb2 using fun τ => exists_block X.p0 (K τ) (hKd τ) (hK0 τ)
  refine ⟨fun τ => b τ, hb, fun τ a c hc ha => (hb1 τ c a hc).trans (hK0 τ c a (by simp [hc, ha])), fun v j => ?_⟩
  obtain ⟨⟨τ, a⟩, rfl⟩ := idx.symm.surjective j
  rw [hK]
  simp only [hfr, Equiv.apply_symm_apply]
  have hm : mat (rmul x fun τ => b τ) τ = mat x τ * b τ := rfl
  rw [hm]
  split_ifs with ha
  · have : FD.col (mat x τ * b τ) a = ∑ c, K τ a c • FD.col (mat x τ) c := by
      ext i
      simp [FD.col, mul_apply, hb1 τ a _ ha, mul_comm]
    rw [this, hermC_sum_left, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hermC_smul_left]
    split_ifs with hc
    · rfl
    · rw [hK0 τ a c (by simp [ha, hc]), zero_mul, zero_mul]
  · rw [Matrix.mul_inv_rev, ← mulVec_mulVec]
    show ∑ c, (b τ)⁻¹ a c * _ = ∑ c, K τ a c * _
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hb2 τ a c ha]
    split_ifs with hc
    · rw [hK0 τ a c (by simp [ha, hc]), zero_mul, zero_mul]
    · rfl

set_option maxHeartbeats 1000000 in

theorem exists_adapted {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (y : FrPt Xo c (CAt σ)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P) (hy : F.u k P = y.x) :
    ∃ (V : Matrix (Fin g) (Fin g) ℂ) (P' : (F.Di k).La →+ (Fin g → ℂ)), IsUnit V.det ∧
      (∀ j j', V j j' ≠ 0 → (e j).1 = (e j').1) ∧ (∀ a, P' a = V *ᵥ P a) ∧
      IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P' ∧ y.x = F.u k P' ∧
      ∀ τ (i : Fin (Dw.mult τ)),
        IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
  classical
  obtain ⟨ht1, ht2, ht3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hw : ∀ j : Fin g, ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (y.u (e j).1 (e j).2) := fun j =>
    (ht3 (y.u (e j).1 (e j).2) (by rw [hy]; exact y.tan _ _)).exists
  choose w hw using hw
  have hw' : ∀ τ (i : Fin (Dw.mult τ)),
      IsDerivAt0 (fun z => (F.ex k P z).left) (w (e.symm ⟨τ, i⟩)) (y.u τ i) := fun τ i => by
    have := hw (e.symm ⟨τ, i⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hsp : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv⟩ := (ht2 (Pi.single j 1)).exists
    have htan := ht1 _ _ hv
    have heig :=
      (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP (Pi.single j 1) v (e j).1 hv).2
        (fun j' hj' => by
          by_contra hne
          exact hj' (Pi.single_eq_of_ne (fun hh => hne (by rw [hh])) _))
    have htan' : IsTanAt y.x v := by rw [← hy]; exact htan
    obtain ⟨a, ha⟩ := (y.basis (e j).1 v htan' heig).exists
    have ha' : IsCombAt (F.u k P) (y.u (e j).1) (show Fin (Dw.mult (e j).1) → ℂ from a) v := by
      rw [hy]; exact ha
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (y.u (e j).1)
      (fun i => w (e.symm ⟨(e j).1, i⟩)) (hw' (e j).1) a v).1 ha'
    exact ⟨a, (ht3 v htan).unique hd hv⟩
  obtain ⟨V, hVu, hVt, hVw⟩ := GlobalTheory.CoverFrame.exists_inverse_block e w hsp
  obtain ⟨P', hP', hP'e⟩ := GlobalTheory.PeriodLin.exists_period_mulVec E H (F.Di k) g _ P V hP hVu
    (fun j j' h => by rw [hVt j j' h])
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hP'e
  refine ⟨V, P', hVu, hVt, hP'e, hP', hy.symm.trans hu, fun τ i => ?_⟩
  have := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P' (Matrix.mulVecLin V) hP' hex
    _ _).1 (hw' τ i)
  rw [Matrix.mulVecLin_apply, hVw] at this
  exact this

theorem exists_frBor {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
    (U : Unf Xo c σ r) (hU : IsUnf U) (hσ : GoodEmb c σ) (k : U.Comp) (x : (U.X k).dom) (y : FrPt Xo c (CAt σ))
    (h : (U.un k x).x = y.x) :
    ∃ b : Frame (U.X k).Ψ r, (∀ τ, (mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < (U.X k).p0 → ¬ (a : ℕ) < (U.X k).p0 → b τ a c = 0) ∧
      ∃ (hb : rmul x.1 b ∈ (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k ⟨_, hb⟩) y := by
  classical
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hΨ⟩ := hty k
  obtain ⟨P, hPe, hP, hx, -, -⟩ := hpt k x
  obtain ⟨V, P', hV, hVt, hP'e, hP', hy, hd⟩ := exists_adapted e F y (ik k) P hP (hx.symm.trans h)
  obtain ⟨b, hb, hb0, hbe⟩ := exists_frame_mulVec (U.X k) (p := Dw.p) (by omega) (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hΨ _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hΨ _).2 ((hrt τ).2 h'))), hp0]) e V hV hVt x.1
  have hm := rmul_mem_dom (U.X k) x.2 b hb hb0
  obtain ⟨P₁, hP₁e, hP₁, hx₁, hd₁, -⟩ := hpt k ⟨_, hm⟩
  obtain ⟨t, ht, -⟩ := GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F (ik k) P' P₁ 1 y
    (U.un k ⟨_, hm⟩) hP' hP₁ (fun a => by
      ext j
      rw [one_mulVec, hP'e, hP₁e, hbe]
      exact congrFun (congrArg (V *ᵥ ·) (funext fun j => (hPe a j).symm)) j)
    (fun j j' hj => by
      obtain rfl : j = j' := by_contra fun hne => hj (one_apply_ne hne)
      exact ⟨rfl, le_rfl⟩) hy hx₁ hd hd₁
  exact ⟨b, hb, hb0, hm, t, ht⟩

end GlobalTheory.PointOfFrames

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

theorem GlobalTheory.PointOfFrames.ptOfFrame_eq_of_point_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r j : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U) (e : Dw.p = j) (Tau : Type) [Fintype Tau] (hr : 0 < r) (T : Tau ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k))) (s : U.Comp → Tau → ℂˣ), Formalism.L2.PjFree.GoodEmb c σ → ∀ (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom), (U.un k x).x = (U.un k' x').x → ptOfFrame (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s k x = ptOfFrame (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s k' x' := by
  intro E _ _ _ H Dw l Xo c σ r j U hU e Tau _ hr T B s hσ k k' x x' h
  obtain ⟨b, hb, hb0, hm, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x _ h
  rw [← ptOfFrame_eq_of_frBor U hU e hr T B s ⟨_, hm⟩ x' ht]
  rw [first_index_eq_of_unfolded U hU e] at hb0
  refine congrArg (Sigma.mk k) (congrArg (Quot.mk _) (Subtype.ext ?_))
  exact (GlobalTheory.PointOfFrames.domPt_rmul_block _ _ _ _ b hb hb0).symm
