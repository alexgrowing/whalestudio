import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityUnipotentProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTriangularConjugateEqDiagonalRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdbarLogDetSubmatrixCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionTraceSubmatrixConnectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagonalEntryConjugateStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens.NormalCoord
variable {m : ℕ}

theorem exists_upper_chg_eq_one {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) :
    ∃ T : Matrix (Fin m) (Fin m) ℂ, (∀ a c : Fin m, c < a → T a c = 0) ∧ chg T M = 1 := by
  have hG : Mᵀ.PosDef := hM.transpose
  set Li := LDL.lowerInv hG with hLi
  have hΔ := LDL.diag_eq_lowerInv_conj hG
  have hLu : IsUnit Li := isUnit_of_invertible _
  have hLHinj : Function.Injective (Liᴴ).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit]; exact hLu.star
  have hdpos : (LDL.diag hG).PosDef := by
    rw [hΔ]
    have := hG.conjTranspose_mul_mul_same hLHinj
    rwa [Matrix.conjTranspose_conjTranspose] at this
  set d := LDL.diagEntries hG with hd
  have hdiag : LDL.diag hG = Matrix.diagonal d := rfl
  have hdp : ∀ i, 0 < d i := fun i => by
    have := hdpos.diag_pos (i := i)
    rwa [hdiag, Matrix.diagonal_apply_eq] at this
  have hdre : ∀ i, d i = ((d i).re : ℂ) := fun i => by
    have := Complex.lt_def.1 (hdp i)
    apply Complex.ext <;> simp [this.2.symm]
  have hdre_pos : ∀ i, 0 < (d i).re := fun i => (Complex.lt_def.1 (hdp i)).1
  set r : Fin m → ℂ := fun i => (((d i).re ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hr
  have hR : (Liᴴ * diagonal r)ᴴ * Mᵀ * (Liᴴ * diagonal r) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose]
    calc diagonal (star r) * Li * Mᵀ * (Liᴴ * diagonal r)
        = diagonal (star r) * (Li * Mᵀ * Liᴴ) * diagonal r := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [← hΔ, hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        simp only [Pi.star_apply, hr, Complex.star_def, Complex.conj_ofReal]
        rw [hdre i]
        have h2 : (d i).re ^ (-(1 / 2 : ℝ)) * (d i).re ^ (-(1 / 2 : ℝ)) * (d i).re = 1 := by
          rw [← Real.rpow_add (hdre_pos i), show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num,
            Real.rpow_neg_one, inv_mul_cancel₀ (hdre_pos i).ne']
        simp only [Complex.ofReal_re]
        rw [show ((((d i).re ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((d i).re : ℂ) *
          (((d i).re ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = ((((d i).re ^ (-(1 / 2 : ℝ)) *
            (d i).re ^ (-(1 / 2 : ℝ)) * (d i).re) : ℝ) : ℂ) by push_cast; ring, h2,
          Complex.ofReal_one]
  refine ⟨Liᴴ * diagonal r, fun i j hji => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.conjTranspose_apply]
    show star (LDL.lowerInv hG j i) * r j = 0
    rw [LDL.lowerInv_triangular hG hji, star_zero, zero_mul]
  · have key : ∀ R : Matrix (Fin m) (Fin m) ℂ, Rᴴ * Mᵀ * R = 1 → chg R M = 1 := fun R h => by
      have := congrArg transpose h
      rw [transpose_one, transpose_mul, transpose_mul, transpose_transpose] at this
      rw [chg, Matrix.mul_assoc]
      exact this
    exact key _ hR

theorem isHermitian_transpose_mul {G F : Matrix (Fin m) (Fin m) ℂ} (hG : G.IsHermitian)
    (hu : IsUnit G.det) (h : adj G G F = F) : (Fᵀ * G).IsHermitian := by
  have hu' : IsUnit Gᵀ.det := by rwa [det_transpose]
  have h1 : Fᴴ * Gᵀ = Gᵀ * F := by
    rw [adj] at h
    calc Fᴴ * Gᵀ = Gᵀ * (Gᵀ⁻¹ * Fᴴ * Gᵀ) := by
          rw [Matrix.mul_assoc Gᵀ⁻¹, mul_nonsing_inv_cancel_left _ _ hu']
      _ = Gᵀ * F := by rw [h]
  have h2 := congrArg transpose h1
  rw [transpose_mul, transpose_mul, transpose_transpose] at h2
  unfold IsHermitian
  rw [conjTranspose_mul, hG.eq]
  exact h2

theorem emb_injective (i : Fin m) : Function.Injective (emb i) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Fin.castLE_injective i.isLt.le h)
  · exact absurd (congrArg Fin.val h) (by simp [emb]; omega)
  · exact absurd (congrArg Fin.val h) (by simp [emb]; omega)
  · exact congrArg Sum.inr (Subsingleton.elim a b)

theorem sum_Iio (i : Fin m) {M : Type*} [AddCommMonoid M] (g : Fin m → M) :
    ∑ c ∈ Finset.Iio i, g c = ∑ a : Fin i, g (Fin.castLE i.isLt.le a) := by
  rw [← Finset.sum_image (g := Fin.castLE i.isLt.le) (fun a _ b _ h => Fin.castLE_injective _ h)]
  congr 1
  ext c
  simp only [Finset.mem_Iio, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hc; exact ⟨⟨c, hc⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩; exact a.isLt

theorem sum_emb (i : Fin m) {M : Type*} [AddCommMonoid M] (f : Fin m → M)
    (hf : ∀ c, i < c → f c = 0) : ∑ c, f c = ∑ u : Fin i ⊕ Fin 1, f (emb i u) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  simp only [emb, Sum.elim_inl, Sum.elim_inr]
  rw [← sum_Iio]
  have e : ∑ c, f c = ∑ c ∈ Finset.Iic i, f c :=
    (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => hf c (by simpa using hc)).symm
  rw [e, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]

theorem sum_low (f : Fin m → Fin m → ℂ) :
    ∑ s : Low m, f s.1.1 s.1.2 = ∑ b, ∑ c ∈ Finset.Iio b, f b c := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun x : Fin m × Fin m => x.2 < x.1)
    (p := fun x : Fin m × Fin m => x.2 < x.1) (by simp) (fun x => f x.1 x.2),
    Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext c <;> simp

theorem chg_submatrix_emb {T M : Matrix (Fin m) (Fin m) ℂ}
    (hT : ∀ a c : Fin m, c < a → T a c = 0) (i : Fin m) :
    (chg T M).submatrix (emb i) (emb i) =
      chg (T.submatrix (emb i) (emb i)) (M.submatrix (emb i) (emb i)) := by
  have hle : ∀ u, emb i u ≤ i := by
    rintro (a | a)
    · exact (Fin.le_def.2 (by simp [emb]))
    · exact le_rfl
  ext x y
  simp only [chg, mul_apply, transpose_apply, submatrix_apply, conjTranspose_apply]
  rw [sum_emb i _ fun c hc => by simp [hT c (emb i y) (lt_of_le_of_lt (hle y) hc)]]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  exact sum_emb i _ fun d hd => by simp [hT d (emb i x) (lt_of_le_of_lt (hle x) hd)]

theorem sum_low_signed (f : Fin m → Fin m → ℂ) (i : Fin m) :
    ∑ s : Low m, ((((if i = s.1.1 then 1 else 0 : ℝ) - if i = s.1.2 then 1 else 0 : ℝ) : ℂ) * f s.1.1 s.1.2) =
      ∑ c ∈ Finset.Iio i, f i c - ∑ c ∈ Finset.Ioi i, f c i := by
  simp only [Complex.ofReal_sub, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [sum_low (fun b c => if i = b then f b c else 0), sum_low (fun b c => if i = c then f b c else 0)]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp only [Finset.sum_ite_eq]
    rw [← Finset.sum_filter]
    congr 1
    ext b; simp

theorem norm_diag_prod_eq_jacDens {m : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hG : G.PosDef) (n : Low m → ℂ)
    (T : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a c : Fin m, c < a → T a c = 0)
    (h1 : chg T (chg (uni n) G) = 1) :
    ∏ s : Low m, ‖T s.1.2 s.1.2 / T s.1.1 s.1.1‖ ^ 2 = jacDens G n :=
  GlobalTheory.T.jacobian_density_unipotent_product G hG n T hT h1

theorem det_low {m : ℕ} (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : ∀ a c : Fin m, c < a → T a c = 0) (hTu : IsUnit T.det) :
    (Matrix.of fun s t : Low m => (T⁻¹ * (uni n)⁻¹) s.1.1 t.1.1 * T t.1.2 s.1.2).det =
      ∏ s : Low m, T s.1.2 s.1.2 / T s.1.1 s.1.1 :=
  GlobalTheory.T.det_triangular_conjugate_eq_diagonal_ratio n T hT hTu

theorem ddbar_rootWt {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (i : Fin N)
    (h2 : MContDiffAt 2 H p) (hp : ∀ᶠ v in 𝓝 p, (H v).PosDef) (h1 : H p = 1) (ξ η : E) :
    ddbar (fun v => ((-Real.log (quotGram ((H v).submatrix (emb i) (emb i))).det.re : ℝ) : ℂ)) p ξ η =
      curv H p ξ η i i + ∑ a ∈ Finset.Iio i, conn H p ξ i a * starRingEnd ℂ (conn H p η i a) -
        ∑ c ∈ Finset.Ioi i, conn H p ξ c i * starRingEnd ℂ (conn H p η c i) :=
  GlobalTheory.T.ddbar_log_det_submatrix_curvature H p i h2 hp h1 ξ η

theorem extTrace_step {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (i : Fin N)
    (h2 : MContDiffAt 2 H p) (hp : ∀ᶠ v in 𝓝 p, (H v).PosDef) (h1 : H p = 1) (ξ η : E) :
    extTrace (fun v => (H v).submatrix (emb i) (emb i)) p ξ η =
      kappa * ∑ a ∈ Finset.Iio i, conn H p ξ i a * starRingEnd ℂ (conn H p η i a) :=
  GlobalTheory.T.extension_trace_submatrix_connection H p i h2 hp h1 ξ η

theorem theta_eq {m : ℕ} (G F : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : ∀ a c : Fin m, c < a → T a c = 0) (h1 : chg T (chg (uni n) G) = 1) (i : Fin m) :
    theta G (-(Fᵀ * G)) n i = (((uni n * T)⁻¹ * F * (uni n * T)) i i).re :=
  GlobalTheory.T.theta_diagonal_entry_conjugate G F n T hT h1 i

theorem conn_zero_vec {k : Type} [Fintype k] [DecidableEq k] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (H : E → Matrix k k ℂ) (z : E) :
    conn H z 0 = 0 := by
  simpa using conn_smul_vec H z 0 0

theorem frame {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (Gm : V 1 → Matrix (Fin k) (Fin k) ℂ) (z : V 1) (hG : MContDiffAt 2 Gm z)
    (hGp : ∀ᶠ u in 𝓝 z, (Gm u).PosDef) (bL : E →L[ℂ] V 1) (X : E → Matrix (Fin k) (Fin k) ℂ)
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

set_option maxHeartbeats 1000000 in

theorem normal_coords : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (G : ∀ a, V 1 → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : V 1), (∀ a, MContDiffAt ∞ (G a) z) → (∀ a, ∀ᶠ u in 𝓝 z, (G a u).PosDef) → ∃ K : ∀ a, Matrix (Fin (r a)) (Fin (r a)) ℂ, (∀ a, (K a).IsHermitian) ∧ ∀ n : ∀ a, Low (r a) → ℂ, ∃ J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖J.det‖ ^ 2 = ∏ a, jacDens (G a z) (n a) ∧ (∀ x : Σ a, Fin (r a), cHess (d + 1) (fun v => (rootWt e G x v : ℂ)) (pt e z n) = chg J (diagonal fun j => (rootDiag (fun x => theta (G x.1 z) (K x.1) (n x.1) x.2) x (e j) : ℂ))) ∧ (∀ a, ∑ i, formMat (extTrace (stepGram e G a i) (pt e z n)) = chg J (diagonal fun j => (bcDiag a (e j) : ℂ))) ∧ chg J (diagonal fun j => (baseDiag (e j) : ℂ)) = diagonal fun j => (baseDiag (e j) : ℂ) := by
  intro ι _ r d e G z hG hP
  set e0 : V 1 := EuclideanSpace.single 0 1 with he0
  have hPz : ∀ a, (G a z).PosDef := fun a => (hP a).self_of_nhds
  have hGu : ∀ a, IsUnit (G a z).det := fun a => (hPz a).det_pos.ne'.isUnit
  have hG2 : ∀ a, MContDiffAt 2 (G a) z := fun a => (hG a).of_le (by norm_cast)
  refine ⟨fun a => -((curv (G a) z e0 e0)ᵀ * G a z), fun a => ?_, fun n => ?_⟩
  · exact (isHermitian_transpose_mul (hPz a).isHermitian (hGu a)
      (adj_curv (hG2 a) ((hP a).mono fun u hu => hu.isHermitian) (hGu a) e0 e0)).neg
  have hU : ∀ a, IsUnit (uni (n a)) := fun a =>
    (isUnit_iff_isUnit_det _).2 (by rw [GlobalTheory.FlagFibre.det_uni]; exact isUnit_one)
  choose T hT hT1 using fun a => exists_upper_chg_eq_one (posDef_chg (hU a) (hPz a))
  set p := pt e z n with hp
  have hbp : base e p = z := base_pt e z n
  have hfp : fib e p = n := fib_pt e z n
  let bL : V (d + 1) →L[ℂ] V 1 := (EuclideanSpace.proj (𝕜 := ℂ) (e.symm none)).smulRight e0
  have hbL : ∀ v, base e v = bL v := fun v => by
    ext j; fin_cases j; simp [base, bL, e0]
  let X : ∀ a, V (d + 1) → Matrix (Fin (r a)) (Fin (r a)) ℂ := fun a v => uni (fib e v a)
  have hX : ∀ a b c, ContDiff ℂ 2 (fun v => X a v b c) := by
    intro a b c
    by_cases h : c < b
    · simp only [X, uni, of_apply, dif_pos h, fib]
      exact (EuclideanSpace.proj (𝕜 := ℂ) (e.symm (some ⟨a, ⟨(b, c), h⟩⟩))).contDiff
    · simp only [X, uni, of_apply, dif_neg h]
      exact contDiff_const
  have hXp : ∀ a, X a p = uni (n a) := fun a => by simp only [X, hfp]
  have hA0u : ∀ a, IsUnit (uni (n a) * T a).det := fun a => by
    have h := congrArg Matrix.det (hT1 a)
    rw [chg_chg, det_chg, det_one] at h
    have : (uni (n a) * T a).det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact this.isUnit
  have hfr := fun a => frame (G a) z (hG2 a) (hP a) bL (X a) (hX a) p (by rw [← hbL, hbp]) (T a)
    (by rw [hXp]; exact hA0u a)
  let H' : ∀ a, V (d + 1) → Matrix (Fin (r a)) (Fin (r a)) ℂ := fun a v => chg (X a v * T a) (G a (bL v))
  have hH'1 : ∀ a, H' a p = 1 := fun a => by
    show chg (X a p * T a) (G a (bL p)) = 1
    rw [hXp, ← hbL, hbp, ← chg_chg, hT1]
  have hstep : ∀ a i v, (H' a v).submatrix (emb i) (emb i) =
      chg ((T a).submatrix (emb i) (emb i)) (stepGram e G a i v) := fun a i v => by
    rw [stepGram, ← chg_submatrix_emb (hT a), chg_chg]
    simp only [H', X, hbL]
  let Lc : Option (Σ a, Low (r a)) → V (d + 1) → ℂ := fun o ξ =>
    o.elim (ξ (e.symm none)) fun y => conn (H' y.1) p ξ y.2.1.1 y.2.1.2
  have hchg : ∀ δ : Option (Σ a, Low (r a)) → ℂ, ∀ j l,
      chg (Matrix.of fun k j => Lc (e k) (EuclideanSpace.single j 1)) (diagonal fun j => δ (e j)) j l =
        δ none * (EuclideanSpace.single j (1 : ℂ) : V (d + 1)) (e.symm none) *
          star ((EuclideanSpace.single l (1 : ℂ) : V (d + 1)) (e.symm none)) +
        ∑ a, ∑ s : Low (r a), δ (some ⟨a, s⟩) * conn (H' a) p (EuclideanSpace.single j 1) s.1.1 s.1.2 *
          star (conn (H' a) p (EuclideanSpace.single l 1) s.1.1 s.1.2) := by
    intro δ j l
    rw [chg, mul_apply]
    simp only [mul_diagonal, transpose_apply, conjTranspose_apply, of_apply]
    rw [← e.symm.sum_comp, Fintype.sum_option, Fintype.sum_sigma]
    simp only [Equiv.apply_symm_apply, Lc, Option.elim]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => by ring

  have hmdel : ∀ a ξ (b c : Fin (r a)), mdel (X a) p ξ b c =
      if h : c < b then ξ (e.symm (some ⟨a, ⟨(b, c), h⟩⟩)) else 0 := by
    intro a ξ b c
    rw [mdel_apply, del_eq_fderiv (((hX a b c).differentiable (by norm_num)) p)]
    by_cases h : c < b
    · have : (fun v => X a v b c) = ⇑(EuclideanSpace.proj (𝕜 := ℂ) (e.symm (some ⟨a, ⟨(b, c), h⟩⟩))) := by
        funext v; simp [X, uni, h, fib]
      rw [this, ContinuousLinearMap.fderiv, dif_pos h]
      simp
    · have : (fun v => X a v b c) = fun _ => (if b = c then 1 else 0 : ℂ) := by
        funext v; simp [X, uni, h]
      rw [this, dif_neg h]
      simp
  have hbLv : ∀ ξ : V (d + 1), bL ξ = ξ (e.symm none) • e0 := fun ξ => by simp [bL]
  have hconn : ∀ a ξ, conn (H' a) p ξ = (uni (n a) * T a)⁻¹ *
      (conn (G a) z (bL ξ) * (uni (n a) * T a) + mdel (X a) p ξ * T a) := fun a ξ => by
    rw [← hXp]; exact (hfr a).2.2.1 ξ
  have hcurv : ∀ a ξ η, curv (H' a) p ξ η = (uni (n a) * T a)⁻¹ * curv (G a) z (bL ξ) (bL η) *
      (uni (n a) * T a) := fun a ξ η => by
    rw [← hXp]; exact (hfr a).2.2.2 ξ η
  have hTu : ∀ a, IsUnit (T a).det := fun a => by
    have := hA0u a
    rwa [det_mul, GlobalTheory.FlagFibre.det_uni, one_mul] at this

  have hHf : ∀ a, MContDiffAt 2 (fun v => chg (uni (fib e v a)) (G a (base e v))) p ∧
      ∀ᶠ v in 𝓝 p, (chg (uni (fib e v a)) (G a (base e v))).PosDef := fun a => by
    have h := frame (G a) z (hG2 a) (hP a) bL (X a) (hX a) p (by rw [← hbL, hbp]) 1
      (by rw [Matrix.mul_one, hXp, GlobalTheory.FlagFibre.det_uni]; exact isUnit_one)
    have hSg : (fun v => chg (X a v * 1) (G a (bL v))) = fun v => chg (uni (fib e v a)) (G a (base e v)) := by
      funext v; simp only [Matrix.mul_one, X, hbL]
    exact ⟨by rw [← hSg]; exact h.1, h.2.1.mono fun v hv => by simpa only [Matrix.mul_one, X, hbL] using hv⟩
  have hT'u : ∀ a (i : Fin (r a)), IsUnit ((T a).submatrix (emb i) (emb i)).det := fun a i => by
    have h := congrArg Matrix.det (hstep a i p)
    rw [hH'1, submatrix_one _ (emb_injective i), det_one, det_chg] at h
    have : ((T a).submatrix (emb i) (emb i)).det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact this.isUnit
  have hT'21 : ∀ a (i : Fin (r a)), ((T a).submatrix (emb i) (emb i)).toBlocks₂₁ = 0 := fun a i => by
    ext x y
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, submatrix_apply, emb, Sum.elim_inl, Sum.elim_inr]
    exact hT a _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; exact y.isLt)
  have hkap : kappa ≠ 0 := by simp [kappa, Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨Matrix.of fun k j => Lc (e k) (EuclideanSpace.single j 1), ?_, ?_, ?_, ?_⟩

  ·
    have hsame : ∀ a (s t : Low (r a)),
        conn (H' a) p (EuclideanSpace.single (e.symm (some ⟨a, t⟩)) 1) s.1.1 s.1.2 =
          ((T a)⁻¹ * (uni (n a))⁻¹) s.1.1 t.1.1 * T a t.1.2 s.1.2 := by
      intro a s t
      have hD : mdel (X a) p (EuclideanSpace.single (e.symm (some ⟨a, t⟩)) 1) =
          of fun b c => if b = t.1.1 ∧ c = t.1.2 then 1 else 0 := by
        ext b c
        rw [hmdel, of_apply]
        by_cases h : c < b
        · rw [dif_pos h, EuclideanSpace.single_apply]
          simp only [EmbeddingLike.apply_eq_iff_eq, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq,
            true_and, Subtype.ext_iff, Prod.ext_iff]
        · rw [dif_neg h, if_neg]
          rintro ⟨rfl, rfl⟩
          exact h t.2
      have h0 : (EuclideanSpace.single (e.symm (some ⟨a, t⟩)) (1 : ℂ) : V (d + 1)) (e.symm none) = 0 := by
        rw [EuclideanSpace.single_apply, if_neg]
        simp
      rw [hconn, hbLv, h0, zero_smul, conn_zero_vec, Matrix.zero_mul, zero_add, hD, Matrix.mul_inv_rev]
      simp [mul_apply, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hdiff : ∀ a (a' : ι) (t : Low (r a')), a' ≠ a →
        conn (H' a) p (EuclideanSpace.single (e.symm (some ⟨a', t⟩)) 1) = 0 := by
      intro a a' t hne
      have hD : mdel (X a) p (EuclideanSpace.single (e.symm (some ⟨a', t⟩)) 1) = 0 := by
        ext b c
        rw [hmdel]
        split_ifs with h
        · rw [EuclideanSpace.single_apply, if_neg]
          · rfl
          simp only [EmbeddingLike.apply_eq_iff_eq, Option.some.injEq, Sigma.mk.inj_iff]
          exact fun h' => hne h'.1.symm
        · rfl
      have h0 : (EuclideanSpace.single (e.symm (some ⟨a', t⟩)) (1 : ℂ) : V (d + 1)) (e.symm none) = 0 := by
        rw [EuclideanSpace.single_apply, if_neg]
        simp
      rw [hconn, hbLv, h0, zero_smul, conn_zero_vec, Matrix.zero_mul, zero_add, hD, Matrix.zero_mul,
        Matrix.mul_zero]
    have hM : ((Matrix.of fun k j => Lc (e k) (EuclideanSpace.single j 1)).submatrix e.symm e.symm).submatrix
        (Equiv.optionEquivSumPUnit (Σ a, Low (r a)) : Option _ ≃ _ ⊕ Unit).symm
          (Equiv.optionEquivSumPUnit (Σ a, Low (r a)) : Option _ ≃ _ ⊕ Unit).symm =
        fromBlocks (blockDiagonal' fun a => Matrix.of fun s t : Low (r a) =>
          ((T a)⁻¹ * (uni (n a))⁻¹) s.1.1 t.1.1 * T a t.1.2 s.1.2)
          (Matrix.of fun y (_ : Unit) => Lc (some y) (EuclideanSpace.single (e.symm none) 1)) 0 1 := by
      ext (⟨a, s⟩ | u) (⟨a', t⟩ | u')
      · simp only [submatrix_apply, of_apply, Equiv.optionEquivSumPUnit_symm_inl, Equiv.apply_symm_apply,
          fromBlocks_apply₁₁]
        by_cases h : a' = a
        · subst h
          rw [blockDiagonal'_apply_eq]
          exact hsame a' s t
        · rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm h)]
          simp only [Lc, Option.elim]
          rw [hdiff a a' t h]
          rfl
      · simp [Lc]
      · simp only [submatrix_apply, of_apply, Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, Equiv.apply_symm_apply, fromBlocks_apply₂₁, Lc, Option.elim]
        rw [EuclideanSpace.single_apply, if_neg]
        · rfl
        simp
      · simp [Lc]
    rw [← det_submatrix_equiv_self e.symm,
      ← det_submatrix_equiv_self (Equiv.optionEquivSumPUnit (Σ a, Low (r a)) : Option _ ≃ _ ⊕ Unit).symm, hM,
      det_fromBlocks_zero₂₁, det_one, mul_one, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod, norm_prod,
      ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [det_low (n a) (T a) (hT a) (hTu a), norm_prod, ← Finset.prod_pow]
    exact norm_diag_prod_eq_jacDens _ (hPz a) (n a) (T a) (hT a) (hT1 a)

  ·
    rintro ⟨a, i⟩
    set S := fun v => (H' a v).submatrix (emb i) (emb i) with hSdef
    have hS2 : MContDiffAt 2 S p := (hfr a).1.submatrix _ _
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
    set w : V (d + 1) → ℝ := fun v => -Real.log (quotGram (S v)).det.re with hwdef
    have hw : ContDiffAt ℝ 2 w p :=
      ((Complex.reCLM.contDiff.contDiffAt.comp p (hS2.quotGram hsub1).det).log hq1).neg
    set T' := (T a).submatrix (emb i) (emb i) with hT'def
    have hT'b : T' = fromBlocks T'.toBlocks₁₁ T'.toBlocks₁₂ 0 T'.toBlocks₂₂ := by
      rw [← hT'21 a i, fromBlocks_toBlocks]
    have hdetT' : T'.det = T'.toBlocks₁₁.det * T a i i := by
      conv_lhs => rw [hT'b]
      rw [det_fromBlocks_zero₂₁, det_unique T'.toBlocks₂₂]
      rfl
    have hA1 : IsUnit T'.toBlocks₁₁.det := by
      have := hT'u a i; rw [← hT'def, hdetT', IsUnit.mul_iff] at this; exact this.1
    have hTii : T a i i ≠ 0 := by
      have := hT'u a i; rw [← hT'def, hdetT', IsUnit.mul_iff] at this; exact this.2.ne_zero
    have he1 : (fun v => rootWt e G ⟨a, i⟩ v) =ᶠ[𝓝 p] fun v => w v + Real.log (‖T a i i‖ ^ 2) := by
      filter_upwards [(hHf a).2] with v hv
      have hsv : (stepGram e G a i v).PosDef := hv.submatrix (emb_injective i)
      have hsub : IsUnit (subGram (stepGram e G a i v)).det :=
        (posDef_subGram hsv).det_pos.ne'.isUnit
      have hq : quotGram (S v) = chg T'.toBlocks₂₂ (quotGram (stepGram e G a i v)) := by
        simp only [hSdef]
        rw [hstep a i v, ← hT'def, hT'b]
        exact quotGram_chg _ _ hA1 hsub
      have hdet : (quotGram (S v)).det.re = ‖T a i i‖ ^ 2 * (quotGram (stepGram e G a i v)).det.re := by
        rw [hq, det_chg, Complex.re_ofReal_mul, det_unique]
        rfl
      have hpos := det_re_pos (posDef_quotGram hsv)
      have hT2 : ‖T a i i‖ ^ 2 ≠ 0 := by positivity
      simp only [hwdef, rootWt, hdet]
      rw [Real.log_mul hT2 hpos.ne']
      ring
    have hC : ∀ ξ η : V (d + 1), curv (H' a) p ξ η i i = ξ (e.symm none) * starRingEnd ℂ (η (e.symm none)) *
        ((uni (n a) * T a)⁻¹ * curv (G a) z e0 e0 * (uni (n a) * T a)) i i := by
      intro ξ η
      have hs := isSesq_curv (hG2 a) (hGu a)
      rw [hcurv, hbLv, hbLv, hs.smul_left, hs.smul_right, smul_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_apply, smul_eq_mul]
    have hCreal : ((((uni (n a) * T a)⁻¹ * curv (G a) z e0 e0 * (uni (n a) * T a)) i i).re : ℂ) =
        ((uni (n a) * T a)⁻¹ * curv (G a) z e0 e0 * (uni (n a) * T a)) i i := by
      set ξ0 : V (d + 1) := EuclideanSpace.single (e.symm none) 1
      have h0 : bL ξ0 = e0 := by rw [hbLv]; simp [ξ0]
      have hadj : adj (H' a p) (H' a p) (curv (H' a) p ξ0 ξ0) = curv (H' a) p ξ0 ξ0 :=
        adj_curv (hfr a).1 ((hfr a).2.1.mono fun v hv => hv.isHermitian)
          (by rw [show chg (X a p * T a) (G a (bL p)) = 1 from hH'1 a, det_one]; exact isUnit_one) ξ0 ξ0
      rw [hH'1 a, hcurv, h0] at hadj
      have := congrFun (congrFun hadj i) i
      simp only [adj, transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, conjTranspose_apply] at this
      exact Complex.conj_eq_iff_re.1 this
    ext j l
    rw [GlobalTheory.CurveDens.cHess_apply_eq_ddbar
      (contDiffAt_ofReal_comp ((hw.add contDiffAt_const).congr_of_eventuallyEq he1)) j l]
    change leviForm (fun v => rootWt e G ⟨a, i⟩ v) p _ _ = _
    rw [leviForm_congr he1, leviForm_add_const _ hw]
    change ddbar (fun v => ((-Real.log (quotGram ((H' a v).submatrix (emb i) (emb i))).det.re : ℝ) : ℂ)) p _ _ = _
    rw [ddbar_rootWt (H' a) p i (hfr a).1 (hfr a).2.1 (hH'1 a), hC]
    rw [hchg (fun o => (rootDiag (fun x => theta (G x.1 z) (-((curv (G x.1) z e0 e0)ᵀ * G x.1 z)) (n x.1) x.2)
      ⟨a, i⟩ o : ℂ))]
    rw [Finset.sum_eq_single a]
    · simp only [rootDiag, Option.elim, Sigma.mk.inj_iff, heq_eq_eq, true_and, mul_assoc]
      rw [sum_low_signed (fun b c => conn (H' a) p (EuclideanSpace.single j 1) b c *
        star (conn (H' a) p (EuclideanSpace.single l 1) b c)) i]
      rw [theta_eq _ _ (n a) (T a) (hT a) (hT1 a)]
      simp only [Matrix.mul_assoc] at hCreal ⊢
      rw [hCreal]
      try simp only [Complex.star_def]
      try rw [Complex.star_def]
      ring
    · intro b _ hb
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [rootDiag, Sigma.mk.inj_iff, Ne.symm hb]
    · simp

  ·
    intro a
    have hstepT : ∀ i : Fin (r a), extTrace (stepGram e G a i) p =
        extTrace (fun v => (H' a v).submatrix (emb i) (emb i)) p := by
      intro i
      have hK1 : MContDiffAt 1 (stepGram e G a i) p :=
        ((hHf a).1.submatrix (emb i) (emb i)).of_le one_le_two
      have hKp : ∀ᶠ v in 𝓝 p, (stepGram e G a i v).PosDef :=
        (hHf a).2.mono fun v hv => hv.submatrix (emb_injective i)
      rw [← extTrace_chg (A := fun _ => (T a).submatrix (emb i) (emb i)) hK1 hKp
        (mContDiffAt_const _) (hT'u a i) (fun η => mdbar_const _ p η) (.of_forall fun _ => hT'21 a i)]
      congr 1
      funext v
      exact (hstep a i v).symm
    ext j l
    rw [Matrix.sum_apply, hchg (fun o => (bcDiag a o : ℂ))]
    simp only [formMat, of_apply, hstepT, extTrace_step (H' a) p _ (hfr a).1 (hfr a).2.1 (hH'1 a),
      mul_div_cancel_left₀ _ hkap]
    rw [← sum_low (fun b c => conn (H' a) p (EuclideanSpace.single j 1) b c *
      starRingEnd ℂ (conn (H' a) p (EuclideanSpace.single l 1) b c))]
    simp only [bcDiag, Option.elim, Complex.ofReal_zero, zero_mul, zero_add]
    rw [Finset.sum_eq_single a]
    · simp [Complex.star_def]
    · intro b _ hb; simp [hb]
    · simp

  ·
    ext j l
    rw [hchg (fun o => (baseDiag o : ℂ))]
    simp only [baseDiag, Option.elim, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, add_zero,
      Complex.ofReal_one, one_mul, EuclideanSpace.single_apply, diagonal_apply]
    by_cases hj : e.symm none = j
    · subst hj
      by_cases hl : e.symm none = l
      · subst hl; simp
      · simp [hl, Ne.symm hl]
    · have hej : e j ≠ none := fun h => hj (by rw [← h, Equiv.symm_apply_apply])
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hej
      by_cases hjl : j = l
      · subst hjl; simp [hj, hy]
      · simp [hj, hjl]

end GlobalTheory.MixDens.NormalCoord

end
