import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
open scoped Matrix

namespace GlobalTheory.FrameNormLie

def Supp {n α : Type} (t : n → α) (w : n → ℕ) (h : Matrix n n ℂ) : Prop :=
  ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j'

theorem Supp.mul {n α : Type} [Fintype n] {t : n → α} {w : n → ℕ} {A B : Matrix n n ℂ}
    (hA : Supp t w A) (hB : Supp t w B) : Supp t w (A * B) := by
  intro j j' hne
  rw [Matrix.mul_apply] at hne
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hc
  exact ⟨(hA _ _ h1).1.trans (hB _ _ h2).1, (hA _ _ h1).2.trans (hB _ _ h2).2⟩

theorem Supp.mul_diag {n α : Type} [Fintype n] {t : n → α} {w : n → ℕ}
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') {A B : Matrix n n ℂ}
    (hA : Supp t w A) (hB : Supp t w B) (a : n) : (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    exact hc (hinj _ _ (hB _ _ h2).1 (le_antisymm (hB _ _ h2).2 (hA _ _ h1).2))
  · simp

theorem norm_diag_eq_one {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] {t : n → α} {w : n → ℕ}
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') {N : Matrix n n ℂ} (hN : Supp t w N) (d : n → ℂ)
    (hd : ∀ j, d j ≠ 0) (h : Nᵀ * (Matrix.diagonal d * N.map (starRingEnd ℂ)) = Matrix.diagonal d) (a : n) :
    ‖N a a‖ = 1 := by
  have h1 : (Matrix.diagonal d * N.map (starRingEnd ℂ) * Matrix.diagonal fun j => (d j)⁻¹)ᵀ * N = 1 := by
    rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, h,
      Matrix.diagonal_mul_diagonal, Matrix.transpose_one, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact mul_inv_cancel₀ (hd j)
  have hu : IsUnit N.det := Matrix.isUnit_det_of_left_inverse h1
  have h2 := PerBor.inv_diag t w hinj N hu hN a
  rw [Matrix.inv_eq_left_inv h1] at h2
  simp only [Matrix.transpose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at h2
  have h3 : N a a ≠ 0 := by
    rw [PerBor.det_of_support t w hinj N hN, isUnit_iff_ne_zero] at hu
    exact Finset.prod_ne_zero_iff.1 hu a (Finset.mem_univ a)
  have h4 : N a a * starRingEnd ℂ (N a a) = 1 := by
    have := hd a
    field_simp at h2
    linear_combination h2
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h4
  have h5 : ‖N a a‖ ^ 2 = 1 := by exact_mod_cast h4
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5

theorem norm_diag_eq {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] {t : n → α} {w : n → ℕ}
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') {A B : Matrix n n ℂ} (hA : Supp t w A) (hB : Supp t w B)
    (hB1 : ∀ j, ‖B j j‖ = 1) (d : n → ℂ) (hd : ∀ j, d j ≠ 0)
    (h : Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ)) = Bᵀ * (Matrix.diagonal d * B.map (starRingEnd ℂ)))
    (a : n) : ‖A a a‖ = 1 := by
  have hu : IsUnit B.det := by
    rw [PerBor.det_of_support t w hinj B hB, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by
      rw [← norm_ne_zero_iff, hB1]; exact one_ne_zero
  have hi : Supp t w B⁻¹ := PerBor.inv_support t w B hu hB
  have h1 := norm_diag_eq_one hinj (hA.mul hi) d hd (by
    have e : B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu]; simp
    have e' : B⁻¹ᵀ * Bᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    calc _ = B⁻¹ᵀ * (Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ))) * B⁻¹.map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᵀ * Bᵀ) * Matrix.diagonal d * (B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ)) := by
          rw [h]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [e, e', Matrix.one_mul, Matrix.mul_one]) a
  rwa [Supp.mul_diag hinj hA hi, PerBor.inv_diag t w hinj B hu hB, norm_mul, norm_inv, hB1, inv_one,
    mul_one] at h1

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

noncomputable def perVec (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (v : Fin r → E) :
    Fin g → ℂ := fun k =>
  if ((idx k).2 : ℕ) < X.p0 then hermC (idx k).1.1 X.Gm (col (mat x (idx k).1) (idx k).2) (Data.emb (idx k).1.1 v)
  else ((mat x (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 v) (idx k).2

noncomputable def diagXi (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (k : Fin g) : ℂ :=
  ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ)

theorem re_xi (X : Data E r) (τ : E →+* ℂ) : (τ (-X.ξ0)).re = 0 := by
  have h := congrArg τ X.ξ0_im
  rw [cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
  have := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re, map_neg] at this ⊢
  linarith

theorem diagXi_ne (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (k : Fin g) : diagXi X idx k ≠ 0 := by
  intro h
  have h1 : ((idx k).1.1 (-X.ξ0)).im = 0 := by
    have : 2 * ((idx k).1.1 (-X.ξ0)).im = 0 := by unfold diagXi at h; exact_mod_cast h
    linarith
  have h2 : (idx k).1.1 (-X.ξ0) = 0 := Complex.ext (re_xi X _) h1
  exact X.ξ0_ne (neg_eq_zero.1 ((map_eq_zero _).1 h2))

theorem im_diag_ortho (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (v w : Fin r → E) :
    (hermForm (Matrix.diagonal (diagXi X idx)) (perVec X idx x v) (perVec X idx x w)).im =
      ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v w) : ℚ) : ℝ) := by
  rw [UnitFrame.trace_eq_sum_re X.Ψ X.cmType]
  let p : (Fin r → E) → X.Ψ × Fin r → ℂ := fun v t =>
    if (t.2 : ℕ) < X.p0 then hermC t.1.1 X.Gm (col (mat x t.1) t.2) (Data.emb t.1.1 v)
    else ((mat x t.1)⁻¹ *ᵥ Data.emb t.1.1 v) t.2
  have h2 : hermForm (Matrix.diagonal (diagXi X idx)) (perVec X idx x v) (perVec X idx x w) =
      ∑ t : X.Ψ × Fin r, ((2 * (t.1.1 (-X.ξ0)).im : ℝ) : ℂ) * (p v t * starRingEnd ℂ (p w t)) := by
    rw [hermForm, dotProduct]
    refine Fintype.sum_equiv idx _ _ fun k => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply]
    simp only [p, RCLike.star_def, perVec, diagXi]
    ring
  rw [h2, Fintype.sum_prod_type, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [p]
  rw [← Finset.mul_sum, Complex.im_ofReal_mul, UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat x τ) (hx τ)]
  have h3 : τ.1 (herm X.Gm v w) = hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w) := by
    simp [hermC, herm, Data.emb, cc, IsCMField.complexEmbedding_complexConj]
  rw [map_mul, h3, Complex.mul_re, re_xi]
  ring

theorem exists_tri_unit {α : Type} [Fintype α] (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {t : Fin g → α}
    {w : Fin g → ℕ} (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (hs : ∀ b ∈ Bor X.Ψ r, Supp t w (PerBor.moveMat X.p0 idx b)) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (hu : IsUnitFr X x) : ∃ T : Matrix (Fin g) (Fin g) ℂ, Supp t w T ∧ (∀ j, ‖T j j‖ = 1) ∧ ∀ v v',
      (hermForm (Matrix.diagonal (diagXi X idx)) (T *ᵥ perVec X idx x v) (T *ᵥ perVec X idx x v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ) := by
  obtain ⟨x₀, b, hb, hgr, hb1, rfl⟩ :=
    (UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx hu
  have h1 : ∀ j, ‖PerBor.moveMat X.p0 idx b j j‖ = 1 := fun j => by
    rw [PerBor.moveMat_diag _ idx hb]
    split_ifs
    · exact hb1 _ _
    · rw [norm_inv, hb1, inv_one]
  have hd : IsUnit (PerBor.moveMat X.p0 idx b).det := by
    rw [PerBor.det_of_support t w hinj _ (hs b hb), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by
      rw [← norm_ne_zero_iff, h1]; exact one_ne_zero
  have h2 : ∀ v, (PerBor.moveMat X.p0 idx b)⁻¹ *ᵥ perVec X idx (rmul x₀ b) v = perVec X idx x₀ v := fun v => by
    rw [PerBor.moveMat_mulVec X.p0 idx hb X.Gm x₀ v (perVec X idx x₀ v) (perVec X idx (rmul x₀ b) v)
      (fun _ => rfl) (fun _ => rfl), Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  refine ⟨(PerBor.moveMat X.p0 idx b)⁻¹, PerBor.inv_support t w _ hd (hs b hb), fun j => ?_, fun v v' => ?_⟩
  · rw [PerBor.inv_diag t w hinj _ hd (hs b hb), norm_inv, h1, inv_one]
  · rw [h2, h2, im_diag_ortho X idx x₀ hgr]

set_option maxHeartbeats 1000000 in

theorem cabs_diag_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → FrBor t (U.un k x) (U.un k' x') → ∀ j, cabs (t (some j) : CAt σ) = 1 := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k k' x x' t hx hx' hB j₀
  obtain ⟨hr, hty0, -, h4, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨γ, -, b, -, hk⟩ := (h4 k k' x x').1 ⟨t, hB⟩
  obtain rfl : k' = k := congrArg Sigma.fst hk
  clear hk
  obtain ⟨hp0, hty⟩ := hty0 k'
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k' x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k').Ψ (U.X k').cmType Dw.p Dw.q r hr
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (U.X k').Ψ × Fin r, ∀ j,
      (Formalism.L2.PjFree.relab c σ (e j).1 ∈ (U.X k').Ψ ∧ (idx j).1.1 = Formalism.L2.PjFree.relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (Formalism.L2.PjFree.relab c σ (e j).1 ∉ (U.X k').Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  have hper : ∀ (x : Frame (U.X k').Ψ r) v j, Formalism.L2.PjFree.perFr (U.X k') x v (Formalism.L2.PjFree.relab c σ (e j).1)
      (e j).2 = perVec (U.X k') idx x v j := by
    intro x v j
    unfold perVec
    have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg a, dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (e j).1) ∈ (U.X k').Ψ from hτ), dif_pos hn]
      rfl
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ b ∈ Bor (U.X k').Ψ r, Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ))
      (PerBor.moveMat (U.X k').p0 idx b) := by
    intro b hb j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · rw [if_neg (by omega)] at h2
      exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by simp only; omega⟩
    · rw [if_neg (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      exact ⟨hbij.1 (by rw [← hcc (Formalism.L2.PjFree.relab c σ (e j).1), ← b1, ← h1, b2, hcc]), by simp only; omega⟩
  obtain ⟨T, hT, hT1, hTf⟩ := exists_tri_unit (U.X k') idx hinj hs x.1 x.2 hx
  obtain ⟨T', hT', hT1', hTf'⟩ := exists_tri_unit (U.X k') idx hinj hs x'.1 x'.2 hx'
  have hPv : ∀ a, P a = perVec (U.X k') idx x.1 (φ k' a : Fin r → E) := fun a => funext fun j =>
    (hP a j).trans (hper _ _ _)
  have hPv' : ∀ a, P' a = perVec (U.X k') idx x'.1 (φ k' a : Fin r → E) := fun a => funext fun j =>
    (hP' a j).trans (hper _ _ _)
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ g _ F (ik k') (ik k') P' P p' p
    (by rw [← hPx, ← hPx', hB.1])
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k' x).u τ) _ (hv τ) (cf τ i)
      ((U.un k' x').u τ i)).1 (hPx ▸ hcf3 τ i)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F _ P' p' _ P h.toLinearMap p hex _ _).1 (hv' τ i)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hAe : ∀ j τ i, A j (e.symm ⟨τ, i⟩) =
      ∑ i', (show ℂ from cf τ i i') * (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) j := by
    intro j τ i
    have := congrFun (hcol τ i) j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply] at this
    exact this
  have hA : Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) A := by
    intro j j' hne
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j'
    rw [hAe] at hne
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hi'
    obtain rfl : j = e.symm ⟨τ, i'⟩ := by
      by_contra hj
      exact h2 (Pi.single_eq_of_ne hj _)
    beta_reduce
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨rfl, ?_⟩
    dsimp only
    by_contra hlt
    exact h1 (hcf2 τ i i' (by rw [Fin.lt_def]; omega))
  have key := UnitDet.eq_of_im_hermForm_eq _ p'.2.2.2.1
    ((T * A)ᵀ * (Matrix.diagonal (diagXi (U.X k') idx) * (T * A).map (starRingEnd ℂ)))
    (T'ᵀ * (Matrix.diagonal (diagXi (U.X k') idx) * T'.map (starRingEnd ℂ))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [← UnitDet.hermForm_mulVec, ← UnitDet.hermForm_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hAv, hAv, ← hh, ← hh, hPv, hPv, hPv', hPv', hTf, hTf', ← hEF, ← hEF, hiso])
  obtain ⟨τ, i⟩ := j₀
  have h1 := norm_diag_eq hinj (hT.mul hA) hT' hT1' _ (diagXi_ne _ idx) key (e.symm ⟨τ, i⟩)
  rw [Supp.mul_diag hinj hT hA, norm_mul, hT1, one_mul, hAe, Finset.sum_eq_single i, Pi.single_eq_same,
    mul_one, hcf1] at h1
  · exact h1
  · intro i' _ hi'
    refine mul_eq_zero_of_right _ (Pi.single_eq_of_ne (fun h0 => hi' ?_) _)
    have := e.symm.injective h0
    exact (eq_of_heq (Sigma.mk.inj this).2).symm
  · simp

end GlobalTheory.FrameNormLie
