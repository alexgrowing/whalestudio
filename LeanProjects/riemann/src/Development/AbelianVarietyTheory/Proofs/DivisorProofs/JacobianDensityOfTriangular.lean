import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens.NormalCoordBase

section Frame

open GlobalTheory.MixDens GlobalTheory.CovTest GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Points

theorem frame_base {n k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (Gm : V n → Matrix (Fin k) (Fin k) ℂ) (z : V n) (hG : MContDiffAt 2 Gm z)
    (hGp : ∀ᶠ u in 𝓝 z, (Gm u).PosDef) (bL : E →L[ℂ] V n) (X : E → Matrix (Fin k) (Fin k) ℂ)
    (hX : ∀ b c, ContDiff ℂ 2 (fun v => X v b c)) (p : E) (hbp : bL p = z)
    (T : Matrix (Fin k) (Fin k) ℂ) (hXu : IsUnit (X p * T).det) :
    MContDiffAt 2 (fun v => chg (X v * T) (Gm (bL v))) p ∧
      (∀ᶠ v in 𝓝 p, (chg (X v * T) (Gm (bL v))).PosDef) ∧
      (∀ ξ, conn (fun v => chg (X v * T) (Gm (bL v))) p ξ =
        (X p * T)⁻¹ * (conn Gm z (bL ξ) * (X p * T) + mdel X p ξ * T)) ∧
      ∀ ξ η, curv (fun v => chg (X v * T) (Gm (bL v))) p ξ η =
        (X p * T)⁻¹ * curv Gm z (bL ξ) (bL η) * (X p * T) := by
  have hA' : ∀ b c, ContDiff ℂ 2 (fun v => (X v * T) b c) := fun b c => by
    simp only [mul_apply]; exact ContDiff.sum fun d _ => (hX b d).mul contDiff_const
  have hA : MContDiffAt 2 (fun v => X v * T) p := fun b c =>
    (hA' b c).contDiffAt.restrict_scalars ℝ
  have hX1 : MContDiffAt 1 X p := fun b c => ((hX b c).contDiffAt.restrict_scalars ℝ).of_le (by norm_num)
  have hA0 : ∀ x η, mdbar (fun v => X v * T) x η = 0 := fun x η => by
    ext b c
    rw [mdbar_apply, dbar_eq_zero (((hA' b c).differentiable (by norm_num)) x)]
    rfl
  have hG' : MContDiffAt 2 Gm (bL p) := hbp ▸ hG
  have hGb : MContDiffAt 2 (fun v => Gm (bL v)) p := fun b c =>
    (hG' b c).comp p (bL.contDiff.contDiffAt.restrict_scalars ℝ)
  have hGu : IsUnit (Gm (bL p)).det := by rw [hbp]; exact hGp.self_of_nhds.det_pos.ne'.isUnit
  refine ⟨(hA.transpose.mul hGb).mul hA.conjTranspose.transpose, ?_, fun ξ => ?_, fun ξ η => ?_⟩
  · filter_upwards [hA.eventually_isUnit hXu, bL.continuous.continuousAt.eventually (hbp ▸ hGp)] with v h1 h2
    exact posDef_chg ((isUnit_iff_isUnit_det _).2 h1) h2
  · have e1 := conn_changeFrame (hGb.of_le one_le_two) hGu (hA.of_le one_le_two) hXu (hA0 p) ξ
    rw [show (fun v => chg (X v * T) (Gm (bL v))) = fun v => (X v * T)ᵀ * Gm (bL v) * (X v * T)ᴴᵀ from rfl, e1,
      conn_comp_holo (hG'.of_le one_le_two) bL.differentiableAt, bL.fderiv, hbp,
      mdel_mul hX1 (mContDiffAt_const T), mdel_const, Matrix.mul_zero, zero_add]
  · have e1 := curv_changeFrame hGb hGu hA hXu (.of_forall (hA0 ·)) ξ η
    rw [show (fun v => chg (X v * T) (Gm (bL v))) = fun v => (X v * T)ᵀ * Gm (bL v) * (X v * T)ᴴᵀ from rfl, e1,
      curv_comp_holo hG' hGu bL.contDiff.contDiffAt, bL.fderiv, hbp]

end Frame

theorem sesq_sum_left {W M : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    {F : W → W → M} (hF : IsSesq F) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → W) (y : W) :
    F (∑ a ∈ s, c a • x a) y = ∑ a ∈ s, c a • F (x a) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hF.smul_left 0 0 y
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hF.add_left, hF.smul_left, ih]

theorem sesq_sum_right {W M : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    {F : W → W → M} (hF : IsSesq F) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → W) (y : W) :
    F y (∑ a ∈ s, c a • x a) = ∑ a ∈ s, starRingEnd ℂ (c a) • F y (x a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hF.smul_right 0 y 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hF.add_right, hF.smul_right, ih]

theorem chg_submatrix_equiv_apply {ι : Type} [Fintype ι] {D : ℕ} (J : Matrix (Fin D) (Fin D) ℂ) (ε : Fin D ≃ ι)
    (N : Matrix ι ι ℂ) (j l : Fin D) :
    chg J (N.submatrix ε ε) j l = ∑ y, ∑ y', J (ε.symm y) j * N y y' * star (J (ε.symm y') l) := by
  simp only [chg, mul_apply, transpose_apply, conjTranspose_apply, submatrix_apply, Finset.sum_mul]
  rw [Finset.sum_comm, ← ε.symm.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← ε.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]

end GlobalTheory.MixDens.NormalCoordBase

namespace GlobalTheory.ArchLim.NormalBase

open GlobalTheory.MixDens.NormalCoordBase
open GlobalTheory.MixDens.NormalCoord (emb_injective chg_submatrix_emb sum_low_signed norm_diag_prod_eq_jacDens det_low
  ddbar_rootWt conn_zero_vec)

set_option maxHeartbeats 1000000 in

theorem normal_coords_base : ∀ (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (G : V n → Matrix (Fin r) (Fin r) ℂ) (ψ : V n → ℝ) (u : V n), MContDiffAt ∞ G u → (∀ᶠ v in 𝓝 u, (G v).PosDef) → ContDiffAt ℝ 2 ψ u → ∀ (x : Low r → ℂ) (T : Matrix (Fin r) (Fin r) ℂ), (∀ a c : Fin r, c < a → T a c = 0) → chg T (chg (uni x) (G u)) = 1 → ∃ J : Matrix (Fin D) (Fin D) ℂ, ‖J.det‖ ^ 2 = jacDens (G u) x ∧ (∀ i : Fin r, cHess D (fun v => (rootWt ε G i v : ℂ)) (pt ε u x) = chg J ((fromBlocks (Matrix.of fun j l : Fin n => ((uni x * T)⁻¹ * curv G u (bas n j) (bas n l) * (uni x * T)) i i) 0 0 (diagonal fun s : Low r => ((if i = s.1.1 then 1 else 0) - if i = s.1.2 then 1 else 0 : ℂ))).submatrix ε ε)) ∧ cHess D (fun v => (ψ (base ε v) : ℂ)) (pt ε u x) = chg J ((fromBlocks (cHess n (fun v => (ψ v : ℂ)) u) 0 0 (0 : Matrix (Low r) (Low r) ℂ)).submatrix ε ε) := by
  intro n r D ε G ψ u hG hP hψ x T hT hT1
  have hPu : (G u).PosDef := hP.self_of_nhds
  have hGu : IsUnit (G u).det := hPu.det_pos.ne'.isUnit
  have hG2 : MContDiffAt 2 G u := hG.of_le (by norm_cast)
  set p := pt ε u x with hp
  have hbp : base ε p = u := base_pt ε u x
  have hfp : fib ε p = x := fib_pt ε u x
  let bL : V D →L[ℂ] V n := LinearMap.toContinuousLinearMap
    { toFun := base ε
      map_add' := fun v w => by ext a; simp [base]
      map_smul' := fun c v => by ext a; simp [base] }
  have hbL : ∀ v, base ε v = bL v := fun v => rfl
  have hbLv : ∀ ξ : V D, bL ξ = ∑ a, ξ (ε.symm (.inl a)) • bas n a := fun ξ => by
    ext b
    simp [← hbL, base, bas, EuclideanSpace.single_apply, Pi.single_apply]
  let X : V D → Matrix (Fin r) (Fin r) ℂ := fun v => uni (fib ε v)
  have hX : ∀ b c, ContDiff ℂ 2 (fun v => X v b c) := by
    intro b c
    by_cases h : c < b
    · simp only [X, uni, of_apply, dif_pos h, fib]
      exact (EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨(b, c), h⟩))).contDiff
    · simp only [X, uni, of_apply, dif_neg h]
      exact contDiff_const
  have hXp : X p = uni x := by simp only [X, hfp]
  have hA0u : IsUnit (uni x * T).det := by
    have h := congrArg Matrix.det hT1
    rw [chg_chg, det_chg, det_one] at h
    have : (uni x * T).det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact this.isUnit
  have hTu : IsUnit T.det := by
    have := hA0u
    rwa [det_mul, GlobalTheory.FlagFibre.det_uni, one_mul] at this
  have hfr := frame_base G u hG2 hP bL X hX p (by rw [← hbL, hbp]) T (by rw [hXp]; exact hA0u)
  let H' : V D → Matrix (Fin r) (Fin r) ℂ := fun v => chg (X v * T) (G (bL v))
  have hH'1 : H' p = 1 := by
    show chg (X p * T) (G (bL p)) = 1
    rw [hXp, ← hbL, hbp, ← chg_chg, hT1]
  have hstep : ∀ i v, (H' v).submatrix (emb i) (emb i) =
      chg (T.submatrix (emb i) (emb i)) ((chg (uni (fib ε v)) (G (base ε v))).submatrix (emb i) (emb i)) := by
    intro i v
    rw [← chg_submatrix_emb hT, chg_chg]
    rfl
  let Lc : Fin n ⊕ Low r → V D → ℂ := fun o ξ =>
    Sum.elim (fun a => ξ (ε.symm (.inl a))) (fun s => conn H' p ξ s.1.1 s.1.2) o
  have hchg : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (δ : Low r → ℂ) (j l : Fin D),
      chg (Matrix.of fun k j => Lc (ε k) (EuclideanSpace.single j 1))
        ((fromBlocks A 0 0 (diagonal δ)).submatrix ε ε) j l =
        (∑ a, ∑ b, (EuclideanSpace.single j (1 : ℂ) : V D) (ε.symm (.inl a)) * A a b *
          star ((EuclideanSpace.single l (1 : ℂ) : V D) (ε.symm (.inl b)))) +
        ∑ s : Low r, δ s * conn H' p (EuclideanSpace.single j 1) s.1.1 s.1.2 *
          star (conn H' p (EuclideanSpace.single l 1) s.1.1 s.1.2) := by
    intro A δ j l
    rw [chg_submatrix_equiv_apply]
    simp only [of_apply, Equiv.apply_symm_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add, diagonal_apply, Lc, Sum.elim_inl, Sum.elim_inr]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
      exact Or.inl (mul_comm _ _)
    · intro b _ hb; simp [Ne.symm hb]
    · simp

  have hmdel : ∀ ξ (b c : Fin r), mdel X p ξ b c =
      if h : c < b then ξ (ε.symm (.inr ⟨(b, c), h⟩)) else 0 := by
    intro ξ b c
    rw [mdel_apply, del_eq_fderiv (((hX b c).differentiable (by norm_num)) p)]
    by_cases h : c < b
    · have : (fun v => X v b c) = ⇑(EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨(b, c), h⟩))) := by
        funext v; simp [X, uni, h, fib]
      rw [this, ContinuousLinearMap.fderiv, dif_pos h]
      simp
    · have : (fun v => X v b c) = fun _ => (if b = c then 1 else 0 : ℂ) := by
        funext v; simp [X, uni, h]
      rw [this, dif_neg h]
      simp
  have hconn : ∀ ξ, conn H' p ξ = (uni x * T)⁻¹ *
      (conn G u (bL ξ) * (uni x * T) + mdel X p ξ * T) := fun ξ => by
    rw [← hXp]; exact hfr.2.2.1 ξ
  have hcurv : ∀ ξ η, curv H' p ξ η = (uni x * T)⁻¹ * curv G u (bL ξ) (bL η) * (uni x * T) := fun ξ η => by
    rw [← hXp]; exact hfr.2.2.2 ξ η
  have hHf : MContDiffAt 2 (fun v => chg (uni (fib ε v)) (G (base ε v))) p ∧
      ∀ᶠ v in 𝓝 p, (chg (uni (fib ε v)) (G (base ε v))).PosDef := by
    have h := frame_base G u hG2 hP bL X hX p (by rw [← hbL, hbp]) 1
      (by rw [Matrix.mul_one, hXp, GlobalTheory.FlagFibre.det_uni]; exact isUnit_one)
    have hSg : (fun v => chg (X v * 1) (G (bL v))) = fun v => chg (uni (fib ε v)) (G (base ε v)) := by
      funext v; simp only [Matrix.mul_one, X, hbL]
    exact ⟨by rw [← hSg]; exact h.1, h.2.1.mono fun v hv => by simpa only [Matrix.mul_one, X, hbL] using hv⟩
  have hT'u : ∀ i : Fin r, IsUnit (T.submatrix (emb i) (emb i)).det := fun i => by
    have h := congrArg Matrix.det (hstep i p)
    rw [hH'1, submatrix_one _ (emb_injective i), det_one, det_chg] at h
    have : (T.submatrix (emb i) (emb i)).det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact this.isUnit
  have hT'21 : ∀ i : Fin r, (T.submatrix (emb i) (emb i)).toBlocks₂₁ = 0 := fun i => by
    ext x y
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, submatrix_apply, GlobalTheory.MixDens.emb, Sum.elim_inl, Sum.elim_inr]
    exact hT _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; exact y.isLt)
  have hbL0 : ∀ t : Low r, bL (EuclideanSpace.single (ε.symm (.inr t)) 1) = 0 := fun t => by
    rw [hbLv]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [EuclideanSpace.single_apply, if_neg (by simp), zero_smul]
  refine ⟨Matrix.of fun k j => Lc (ε k) (EuclideanSpace.single j 1), ?_, ?_, ?_⟩
  ·
    have hsame : ∀ s t : Low r,
        conn H' p (EuclideanSpace.single (ε.symm (.inr t)) 1) s.1.1 s.1.2 =
          (T⁻¹ * (uni x)⁻¹) s.1.1 t.1.1 * T t.1.2 s.1.2 := by
      intro s t
      have hD : mdel X p (EuclideanSpace.single (ε.symm (.inr t)) 1) =
          of fun b c => if b = t.1.1 ∧ c = t.1.2 then 1 else 0 := by
        ext b c
        rw [hmdel, of_apply]
        by_cases h : c < b
        · rw [dif_pos h, EuclideanSpace.single_apply]
          simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Subtype.ext_iff, Prod.ext_iff]
        · rw [dif_neg h, if_neg]
          rintro ⟨rfl, rfl⟩
          exact h t.2
      rw [hconn, hbL0, conn_zero_vec, Matrix.zero_mul, zero_add, hD, Matrix.mul_inv_rev]
      simp [mul_apply, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hM : (Matrix.of fun k j => Lc (ε k) (EuclideanSpace.single j 1)).submatrix ε.symm ε.symm =
        fromBlocks 1 0 (Matrix.of fun (s : Low r) (b : Fin n) => Lc (.inr s) (EuclideanSpace.single (ε.symm (.inl b)) 1))
          (Matrix.of fun s t : Low r => (T⁻¹ * (uni x)⁻¹) s.1.1 t.1.1 * T t.1.2 s.1.2) := by
      ext (a | s) (b | t)
      · simp [Lc, EuclideanSpace.single_apply, one_apply]
      · simp [Lc, EuclideanSpace.single_apply]
      · simp [Lc]
      · simp only [submatrix_apply, of_apply, Equiv.apply_symm_apply, fromBlocks_apply₂₂, Lc, Sum.elim_inr]
        exact hsame s t
    rw [← det_submatrix_equiv_self ε.symm, hM, det_fromBlocks_zero₁₂, det_one, one_mul, det_low x T hT hTu,
      norm_prod, ← Finset.prod_pow]
    exact norm_diag_prod_eq_jacDens _ hPu x T hT hT1
  ·
    intro i
    set S := fun v => (H' v).submatrix (emb i) (emb i) with hSdef
    set K := fun v => (chg (uni (fib ε v)) (G (base ε v))).submatrix (emb i) (emb i) with hKdef
    have hS2 : MContDiffAt 2 S p := hfr.1.submatrix _ _
    have hS1 : S p = 1 := by
      simp only [hSdef]; rw [hH'1, submatrix_one _ (emb_injective i)]
    have hs1 : subGram (1 : Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ) = 1 := by
      ext; simp [subGram, toBlocks₁₁, one_apply]
    have hq1' : quotGram (1 : Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ) = 1 := by
      ext; simp [quotGram, toBlocks₂₁, toBlocks₂₂, toBlocks₁₂, toBlocks₁₁, mul_apply, one_apply]
    have hsub1 : IsUnit (subGram (S p)).det := by
      rw [hS1, hs1, det_one]; exact isUnit_one
    have hq1 : (quotGram (S p)).det.re ≠ 0 := by
      rw [hS1, hq1', det_one]; simp
    set w : V D → ℝ := fun v => -Real.log (quotGram (S v)).det.re with hwdef
    have hw : ContDiffAt ℝ 2 w p :=
      ((Complex.reCLM.contDiff.contDiffAt.comp p (hS2.quotGram hsub1).det).log hq1).neg
    set T' := T.submatrix (emb i) (emb i) with hT'def
    have hT'b : T' = fromBlocks T'.toBlocks₁₁ T'.toBlocks₁₂ 0 T'.toBlocks₂₂ := by
      rw [← hT'21 i, fromBlocks_toBlocks]
    have hdetT' : T'.det = T'.toBlocks₁₁.det * T i i := by
      conv_lhs => rw [hT'b]
      rw [det_fromBlocks_zero₂₁, det_unique T'.toBlocks₂₂]
      rfl
    have hA1 : IsUnit T'.toBlocks₁₁.det := by
      have := hT'u i; rw [← hT'def, hdetT', IsUnit.mul_iff] at this; exact this.1
    have hTii : T i i ≠ 0 := by
      have := hT'u i; rw [← hT'def, hdetT', IsUnit.mul_iff] at this; exact this.2.ne_zero
    have he1 : (fun v => rootWt ε G i v) =ᶠ[𝓝 p] fun v => w v + Real.log (‖T i i‖ ^ 2) := by
      filter_upwards [hHf.2] with v hv
      have hsv : (K v).PosDef := hv.submatrix (emb_injective i)
      have hsub : IsUnit (subGram (K v)).det :=
        (posDef_subGram hsv).det_pos.ne'.isUnit
      have hq : quotGram (S v) = chg T'.toBlocks₂₂ (quotGram (K v)) := by
        simp only [hSdef]
        rw [hstep i v, ← hT'def, hT'b]
        exact quotGram_chg _ _ hA1 hsub
      have hdet : (quotGram (S v)).det.re = ‖T i i‖ ^ 2 * (quotGram (K v)).det.re := by
        rw [hq, det_chg, Complex.re_ofReal_mul, det_unique]
        rfl
      have hpos := det_re_pos (posDef_quotGram hsv)
      have hT2 : ‖T i i‖ ^ 2 ≠ 0 := by positivity
      simp only [hwdef, rootWt, hdet]
      rw [Real.log_mul hT2 hpos.ne']
      ring
    have hC : ∀ ξ η : V D, curv H' p ξ η i i = ∑ a, ∑ b, ξ (ε.symm (.inl a)) *
        ((uni x * T)⁻¹ * curv G u (bas n a) (bas n b) * (uni x * T)) i i * star (η (ε.symm (.inl b))) := by
      intro ξ η
      have hs := isSesq_curv hG2 hGu
      rw [hcurv, hbLv, hbLv, sesq_sum_left hs]
      simp only [sesq_sum_right hs, Finset.smul_sum, smul_smul, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.star_def]
      ring
    ext j l
    rw [GlobalTheory.CurveDens.cHess_apply_eq_ddbar
      (contDiffAt_ofReal_comp ((hw.add contDiffAt_const).congr_of_eventuallyEq he1)) j l]
    change leviForm (fun v => rootWt ε G i v) p _ _ = _
    rw [leviForm_congr he1, leviForm_add_const _ hw]
    change ddbar (fun v => ((-Real.log (quotGram ((H' v).submatrix (emb i) (emb i))).det.re : ℝ) : ℂ)) p _ _ = _
    rw [ddbar_rootWt H' p i hfr.1 hfr.2.1 hH'1, hC, hchg]
    have hsig : ∀ s : Low r, ((if i = s.1.1 then 1 else 0) - (if i = s.1.2 then 1 else 0) : ℂ) =
        ((((if i = s.1.1 then 1 else 0 : ℝ) - if i = s.1.2 then 1 else 0 : ℝ) : ℂ)) := by
      intro s; split_ifs <;> simp
    simp only [hsig, mul_assoc]
    rw [sum_low_signed (fun b c => conn H' p (EuclideanSpace.single j 1) b c *
      star (conn H' p (EuclideanSpace.single l 1) b c)) i]
    simp only [of_apply, Complex.star_def]
    ring
  ·
    have hψb : ContDiffAt ℝ 2 ψ (bL p) := by rw [← hbL, hbp]; exact hψ
    have hψc0 : ContDiffAt ℝ 2 (fun w => (ψ w : ℂ)) u := contDiffAt_ofReal_comp hψ
    have hψc : ContDiffAt ℝ 2 (fun v => (ψ (base ε v) : ℂ)) p :=
      contDiffAt_ofReal_comp (hψb.comp p ((bL.contDiff.restrict_scalars ℝ).contDiffAt))
    ext j l
    rw [GlobalTheory.CurveDens.cHess_apply_eq_ddbar hψc j l]
    rw [show (fun v => (ψ (base ε v) : ℂ)) = fun v => (fun w => (ψ w : ℂ)) (bL v) from rfl,
      ddbar_comp_holo (contDiffAt_ofReal_comp hψb) bL.contDiff.contDiffAt, bL.fderiv, ← hbL, hbp, hbLv, hbLv,
      show (0 : Matrix (Low r) (Low r) ℂ) = diagonal 0 from diagonal_zero.symm, hchg]
    simp only [map_sum, map_smul, map_smulₛₗ, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, smul_eq_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.CurveDens.cHess_apply_eq_ddbar hψc0 a b]
    simp only [bas, Complex.star_def, RingHom.id_apply]
    ring

end GlobalTheory.ArchLim.NormalBase
