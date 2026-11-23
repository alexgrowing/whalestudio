import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SecToC
open Ad3.K.LC Ad3.K.LC.B

theorem comp_lin {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E →ₗ[ℝ] E) (hL : LinearMap.det L ≠ 0) (F : E → V) :
    (∫ x, F (L x) ∂μ = |(LinearMap.det L)⁻¹| • ∫ x, F x ∂μ) ∧
      (Integrable F μ → Integrable (fun x => F (L x)) μ) := by
  let e : E ≃ₜ E := (LinearMap.equivOfDetNeZero L hL).toContinuousLinearEquiv.toHomeomorph
  have hef : (e : E → E) = L := rfl
  have hmap : Measure.map L μ = ENNReal.ofReal |(LinearMap.det L)⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hL
  have hpos : 0 ≤ |(LinearMap.det L)⁻¹| := abs_nonneg _
  constructor
  · have h1 : ∫ x, F (L x) ∂μ = ∫ y, F y ∂(Measure.map L μ) := by
      rw [← hef, e.measurableEmbedding.integral_map]
    rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]
  · intro hF
    have h2 : Integrable F (Measure.map L μ) := by
      rw [hmap]
      exact hF.smul_measure ENNReal.ofReal_ne_top
    rw [← hef] at h2
    exact (e.measurableEmbedding.integrable_map_iff.1 h2)

def rowL (v : Fin 2 → ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun j => (v j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j)

theorem rowL_apply (v x : Fin 2 → ℂ) (j : Fin 2) : rowL v x j = v j * x j := by
  simp [rowL]

theorem det_rowL (v : Fin 2 → ℂ) : LinearMap.det (rowL v) = v 0 * v 1 := by
  rw [rowL, LinearMap.det_pi]
  simp [Fin.prod_univ_two]

def matL (v : Fin 2 → ℂ) : M22 →ₗ[ℂ] M22 :=
  LinearMap.pi fun i => (rowL v).comp (LinearMap.proj i)

theorem det_matL (v : Fin 2 → ℂ) : LinearMap.det (matL v) = (v 0 * v 1) ^ 2 := by
  rw [matL, LinearMap.det_pi]
  simp [det_rowL, sq]

theorem normSq_det (z : ℂ) : Algebra.norm ℝ z = ‖z‖ ^ 2 := by
  rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem integral_scale : ∀ (F : Ad3.K.LC.M22 × ℂ → ℝ) (c d e : ℂ), c ≠ 0 → d ≠ 0 → e ≠ 0 → Integrable F →
    Integrable (fun p : Ad3.K.LC.M22 × ℂ =>
      F (Matrix.of.symm (Matrix.of p.1 * Matrix.diagonal ![c, d]), e * p.2)) ∧
    ∫ p : Ad3.K.LC.M22 × ℂ, F (Matrix.of.symm (Matrix.of p.1 * Matrix.diagonal ![c, d]), e * p.2) =
      (‖c‖ ^ 4 * ‖d‖ ^ 4 * ‖e‖ ^ 2)⁻¹ * ∫ p, F p := by
  intro F c d e hc hd he hF
  set L : M22 × ℂ →ₗ[ℂ] M22 × ℂ := (matL ![c, d]).prodMap (e • LinearMap.id) with hL
  have hdet : LinearMap.det (L.restrictScalars ℝ) = ‖c‖ ^ 4 * ‖d‖ ^ 4 * ‖e‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, hL, LinearMap.det_prodMap, det_matL, LinearMap.det_smul,
      LinearMap.det_id, normSq_det]
    simp only [norm_mul, norm_pow, Module.finrank_self, pow_one, mul_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hpos : 0 < ‖c‖ ^ 4 * ‖d‖ ^ 4 * ‖e‖ ^ 2 := by positivity
  have hfun : ∀ p : M22 × ℂ, (Matrix.of.symm (Matrix.of p.1 * Matrix.diagonal ![c, d]), e * p.2) =
      (L.restrictScalars ℝ) p := by
    rintro ⟨h, t⟩
    refine Prod.ext ?_ (by simp [hL])
    funext i j
    simp only [hL, LinearMap.coe_restrictScalars, LinearMap.prodMap_apply, matL, LinearMap.pi_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, rowL_apply]
    simp [Matrix.mul_diagonal, mul_comm]
  have : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure M22).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (M22 × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨h1, h2⟩ := comp_lin (volume : Measure (M22 × ℂ)) (L.restrictScalars ℝ) (by rw [hdet]; exact hpos.ne') F
  simp only [hfun]
  refine ⟨h2 hF, ?_⟩
  rw [h1, hdet, abs_of_pos (inv_pos.2 hpos), smul_eq_mul]

theorem inn_torus : ∀ (Ψ : Ad3.K.LC.Sw) (a b : ℂˣ) (o : GL (Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ),
    Ad3.K.LC.inn Ψ (Ad3.dg (a * b) b 1 * o) h t =
      ((‖(a : ℂ)‖ ^ 4 * ‖(b : ℂ)‖ ^ 4 : ℝ) : ℂ) *
        Ad3.K.LC.B.innB (Ad3.K.LC.B.rt o (Ψ : Ad3.K.LC.B.E5 → ℂ))
          (Matrix.of.symm (h * Matrix.diagonal ![(a : ℂ) * b, (b : ℂ)])) ((a : ℂ) * b * t) a b := by
  intro Ψ a b o h t
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have hb : (b : ℂ) ≠ 0 := b.ne_zero
  set L : (Fin 2 → ℂ) × ℂ →ₗ[ℂ] (Fin 2 → ℂ) × ℂ :=
    (rowL ![(a : ℂ) * b, (b : ℂ)]).prodMap ((a : ℂ) • LinearMap.id) with hL
  have hdet : LinearMap.det (L.restrictScalars ℝ) = ‖(a : ℂ)‖ ^ 4 * ‖(b : ℂ)‖ ^ 4 := by
    rw [LinearMap.det_restrictScalars, hL, LinearMap.det_prodMap, det_rowL, LinearMap.det_smul,
      LinearMap.det_id, normSq_det]
    simp only [norm_mul, Module.finrank_self, pow_one, mul_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hpos : 0 < ‖(a : ℂ)‖ ^ 4 * ‖(b : ℂ)‖ ^ 4 := by
    have := norm_pos_iff.2 ha
    have := norm_pos_iff.2 hb
    positivity
  set δ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(a : ℂ) * b, (b : ℂ)] with hδ
  set g : GL (Fin 3) ℂ := Ad3.dg (a * b) b 1 * o with hg
  set G : (Fin 2 → ℂ) × ℂ → ℂ := fun p =>
    Ψ (Matrix.of.symm (h * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 h) *
      Ad3.K.psiC (-(p.1 1)) * Ad3.K.psiC (-p.2) with hG
  have : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  have h1 := (comp_lin (volume : Measure ((Fin 2 → ℂ) × ℂ)) (L.restrictScalars ℝ)
    (by rw [hdet]; exact hpos.ne') G).1
  have hδinv : δ⁻¹ = Matrix.diagonal ![((a : ℂ) * b)⁻¹, (b : ℂ)⁻¹] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hδ, hb] <;> field_simp
  have hpt : ∀ p : (Fin 2 → ℂ) × ℂ,
      rt o (Ψ : E5 → ℂ) (Matrix.of.symm (Matrix.of (Matrix.of.symm (h * δ)) * blk p.1),
          rowv ((a : ℂ) * b * t) p.2 (Matrix.of (Matrix.of.symm (h * δ)))) *
        Ad3.K.psiC (-((b : ℂ) * p.1 1)) * Ad3.K.psiC (-((a : ℂ) * p.2)) =
      G ((L.restrictScalars ℝ) p) := by
    rintro ⟨x, y⟩
    have e1 : blk (rowL ![(a : ℂ) * b, (b : ℂ)] x) *
        ((Ad3.dg (a * b) b 1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = δ * blk x := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [blk, Ad3.dg, hδ, rowL_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]
    have e2 : rowv ((a : ℂ) * b * t) y (h * δ) = rowv t ((a : ℂ) * y) h := by
      unfold rowv
      rw [Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul, hδinv]
      congr 1
      ext j
      fin_cases j <;> simp [Matrix.vecMul_diagonal] <;> field_simp
    have e3 : h * blk (rowL ![(a : ℂ) * b, (b : ℂ)] x) * (g : Matrix (Fin 3) (Fin 3) ℂ) =
        h * δ * blk x * (o : Matrix (Fin 3) (Fin 3) ℂ) := by
      rw [hg, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc h, e1, ← Matrix.mul_assoc]
    simp only [hG, hL, LinearMap.coe_restrictScalars, LinearMap.prodMap_apply, e3, rt]
    simp only [Equiv.apply_symm_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, e2, rowL_apply]
    rfl
  have hi : innB (rt o (Ψ : E5 → ℂ)) (Matrix.of.symm (h * δ)) ((a : ℂ) * b * t) a b =
      ∫ p, G ((L.restrictScalars ℝ) p) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hi, h1, hdet, abs_of_pos (inv_pos.2 hpos), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
  rfl

noncomputable def rM (m : Matrix (Fin 3) (Fin 3) ℂ) : M23 →ₗ[ℝ] M23 where
  toFun X := Matrix.of.symm (Matrix.of X * m)
  map_add' X Y := by
    show Matrix.of.symm ((Matrix.of X + Matrix.of Y) * m) =
      Matrix.of.symm (Matrix.of X * m) + Matrix.of.symm (Matrix.of Y * m)
    rw [Matrix.add_mul]
    rfl
  map_smul' c X := by
    show Matrix.of.symm ((c • Matrix.of X) * m) = c • Matrix.of.symm (Matrix.of X * m)
    rw [Matrix.smul_mul]
    rfl

theorem norm_rM_le (m : Matrix (Fin 3) (Fin 3) ℂ) (hm : ∀ i j, ‖m i j‖ ≤ 1) (X : M23) :
    ‖rM m X‖ ≤ 3 * ‖X‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hX : ∀ k, ‖X i k‖ ≤ ‖X‖ := fun k => (norm_le_pi_norm (X i) k).trans (norm_le_pi_norm X i)
  have hterm : ∀ k, ‖X i k * m k j‖ ≤ ‖X‖ := fun k => by
    rw [norm_mul]
    calc ‖X i k‖ * ‖m k j‖ ≤ ‖X‖ * 1 :=
          mul_le_mul (hX k) (hm k j) (norm_nonneg _) (norm_nonneg _)
      _ = ‖X‖ := mul_one _
  have hexp : rM m X i j = X i 0 * m 0 j + X i 1 * m 1 j + X i 2 * m 2 j := by
    simp [rM, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hexp]
  calc _ ≤ ‖X i 0 * m 0 j‖ + ‖X i 1 * m 1 j‖ + ‖X i 2 * m 2 j‖ := norm_add₃_le
    _ ≤ 3 * ‖X‖ := by linarith [hterm 0, hterm 1, hterm 2]

noncomputable def tM (m : Matrix (Fin 3) (Fin 3) ℂ) : E5 →L[ℝ] E5 :=
  (LinearMap.toContinuousLinearMap (rM m)).prodMap (ContinuousLinearMap.id ℝ (Fin 2 → ℂ))

theorem norm_tM_le (m : Matrix (Fin 3) (Fin 3) ℂ) (hm : ∀ i j, ‖m i j‖ ≤ 1) (p : E5) :
    ‖tM m p‖ ≤ 3 * ‖p‖ := by
  have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  refine max_le ?_ ?_
  · exact (norm_rM_le m hm p.1).trans (by linarith)
  · show ‖p.2‖ ≤ _
    linarith [norm_nonneg p]

theorem tM_tM (m m' : Matrix (Fin 3) (Fin 3) ℂ) (h : m * m' = 1) (p : E5) : tM m' (tM m p) = p := by
  rcases p with ⟨X, v⟩
  refine Prod.ext ?_ rfl
  show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of X * m)) * m') = X
  simp [Matrix.mul_assoc, h]

theorem entry_le (o : GL (Fin 3) ℂ) (ho : o ∈ Ad3.K.U3) (i j : Fin 3) :
    ‖(o : Matrix (Fin 3) (Fin 3) ℂ) i j‖ ≤ 1 := by
  have h1 : (o.val * o.valᴴ) i i = 1 := by
    rw [show o.val * o.valᴴ = 1 from ho, Matrix.one_apply_eq]
  have h2 : ∑ k, ‖o.val i k‖ ^ 2 = 1 := by
    have : ((∑ k, ‖o.val i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1, Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    exact_mod_cast this
  have h3 : ‖o.val i j‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => ‖o.val i k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  nlinarith [norm_nonneg (o.val i j)]

theorem rt_uniform : ∀ (N M : ℕ) (Ψ : Ad3.K.LC.Sw), ∃ B : ℝ, ∀ o ∈ Ad3.K.U3,
    ContDiff ℝ (⊤ : ℕ∞) (Ad3.K.LC.B.rt o (Ψ : Ad3.K.LC.B.E5 → ℂ)) ∧
    ∀ n ≤ N, ∀ X : Ad3.K.LC.B.E5,
      (1 + ‖X‖) ^ M * ‖iteratedFDeriv ℝ n (Ad3.K.LC.B.rt o (Ψ : Ad3.K.LC.B.E5 → ℂ)) X‖ ≤ B := by
  intro N M Ψ
  set S : ℝ := 2 ^ M * (Finset.Iic (M, N)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hS
  refine ⟨3 ^ M * 3 ^ N * S, fun o ho => ?_⟩
  set T := tM (o : Matrix (Fin 3) (Fin 3) ℂ) with hT
  have hm := entry_le o ho
  have hm' : ∀ i j, ‖(o : Matrix (Fin 3) (Fin 3) ℂ)ᴴ i j‖ ≤ 1 := fun i j => by
    rw [Matrix.conjTranspose_apply, norm_star]
    exact hm j i
  have hrt : rt o (Ψ : E5 → ℂ) = (Ψ : E5 → ℂ) ∘ T := rfl
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Ψ : E5 → ℂ) := Ψ.smooth _
  refine ⟨by rw [hrt]; exact hsm.comp T.contDiff, fun n hn X => ?_⟩
  have hTn : ‖T‖ ≤ 3 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_tM_le _ hm)
  have hX : 1 + ‖X‖ ≤ 3 * (1 + ‖T X‖) := by
    have h := norm_tM_le _ hm' (T X)
    rw [tM_tM _ _ ho] at h
    linarith
  have hit : ‖iteratedFDeriv ℝ n ((Ψ : E5 → ℂ) ∘ T) X‖ ≤ ‖iteratedFDeriv ℝ n (Ψ : E5 → ℂ) (T X)‖ * 3 ^ N := by
    rw [T.iteratedFDeriv_comp_right (hsm.of_le (by exact_mod_cast le_top)) X (le_refl (n : WithTop ℕ∞))]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖T‖ ^ n ≤ 3 ^ n := pow_le_pow_left₀ (norm_nonneg _) hTn n
      _ ≤ 3 ^ N := pow_le_pow_right₀ (by norm_num) hn
  have hsch := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, N)) (k := M) (n := n) le_rfl hn Ψ (T X)
  rw [hrt]
  calc (1 + ‖X‖) ^ M * ‖iteratedFDeriv ℝ n ((Ψ : E5 → ℂ) ∘ T) X‖
      ≤ (3 * (1 + ‖T X‖)) ^ M * (‖iteratedFDeriv ℝ n (Ψ : E5 → ℂ) (T X)‖ * 3 ^ N) := by
        gcongr
    _ = 3 ^ M * 3 ^ N * ((1 + ‖T X‖) ^ M * ‖iteratedFDeriv ℝ n (Ψ : E5 → ℂ) (T X)‖) := by
        rw [mul_pow]; ring
    _ ≤ 3 ^ M * 3 ^ N * S := by
        gcongr

theorem jm_nonneg (N : ℕ) (h : M22) (t α β : ℂ) : 0 ≤ jm N h t α β := by
  unfold jm
  positivity

theorem norm_ph (n : ℤ) (z : ℂ) (hz : z ≠ 0) : ‖ph n z‖ = 1 := by
  have h : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz)]
  unfold ph
  rw [norm_zpow, h, _root_.one_zpow]

theorem det_g (a b : ℂˣ) (o : GL (Fin 3) ℂ) (ho : o ∈ Ad3.K.U3) :
    ‖((Ad3.dg (a * b) b 1 * o : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 =
      ‖(a : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ 4 := by
  have hu : ‖(o : Matrix (Fin 3) (Fin 3) ℂ).det‖ = 1 := by
    have h1 : (o.val * o.valᴴ).det = 1 := by rw [show o.val * o.valᴴ = 1 from ho, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_conjTranspose] at h1
    have h2 : ‖o.val.det‖ ^ 2 = 1 := by
      have := congrArg norm h1
      simpa [norm_mul, norm_star, sq] using this
    nlinarith [norm_nonneg o.val.det, sq_nonneg (‖o.val.det‖ - 1)]
  have hd : ((Ad3.dg (a * b) b 1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det = (a : ℂ) * b * b := by
    simp [Ad3.dg, Matrix.det_fin_three]
  rw [Units.val_mul, Matrix.det_mul, hd, norm_mul, hu]
  simp only [norm_mul]
  ring

theorem main : Ad3.K.LC.B.IbpBound → Ad3.K.LC.B.MajScaled → Ad3.K.LC.B.SecFub → Ad3.K.LC.B.SecTo := by
  intro hI hM hF k hk Ψ ε hε
  obtain ⟨N, hN⟩ := hM ε hε
  obtain ⟨C₂, hC₂⟩ := hN N le_rfl
  obtain ⟨C₁, hC₁⟩ := hI N
  obtain ⟨B, hB⟩ := rt_uniform (2 * N) (2 * N + 20) Ψ
  refine ⟨|C₁ * B| * C₂, ?_⟩
  intro a b o ho
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have hb : (b : ℂ) ≠ 0 := b.ne_zero
  have ha' : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 ha
  have hb' : 0 < ‖(b : ℂ)‖ := norm_pos_iff.2 hb
  set G : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b with hG
  obtain ⟨hGi, hGle⟩ := hC₂ a b ha hb
  set g : GL (Fin 3) ℂ := Ad3.dg (a * b) b 1 * o with hg
  set δ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(a : ℂ) * b, (b : ℂ)] with hδ
  have hdδ : δ.det = (a : ℂ) * b * b := by simp [hδ]
  obtain ⟨hGLi, hGLe⟩ := integral_scale G ((a : ℂ) * b) b ((a : ℂ) * b) (mul_ne_zero ha hb) hb (mul_ne_zero ha hb) hGi
  set GL' : M22 × ℂ → ℝ := fun p => G (Matrix.of.symm (Matrix.of p.1 * δ), (a : ℂ) * b * p.2) with hGL'
  have hpt : ∀ p : M22 × ℂ, ‖secI k Ψ g p‖ ≤
      (‖(a : ℂ)‖ ^ 6 * ‖(b : ℂ)‖ ^ 8 * |C₁ * B|) * GL' p := by
    rintro ⟨h, t⟩
    have hGnn : 0 ≤ GL' (h, t) := by
      simp only [hGL', hG]
      exact mul_nonneg (by positivity) (jm_nonneg _ _ _ _ _)
    have hR : 0 ≤ (‖(a : ℂ)‖ ^ 6 * ‖(b : ℂ)‖ ^ 8 * |C₁ * B|) * GL' (h, t) := by positivity
    by_cases hdet : (Matrix.of h).det = 0
    · simpa [secI, hdet, Real.zero_rpow] using hR
    by_cases ht : t = 0
    · have hk' : (4 * (k : ℤ) - 4) ≠ 0 := by omega
      have h0 : ph (4 * (k : ℤ) - 4) (0 : ℂ) = 0 := by
        simp only [ph, zero_div]; exact _root_.zero_zpow _ hk'
      simpa [secI, ht, h0] using hR
    have hdet' : 0 < ‖(Matrix.of h).det‖ := norm_pos_iff.2 hdet
    have hdh : (Matrix.of (Matrix.of.symm (Matrix.of h * δ))).det = (Matrix.of h).det * ((a : ℂ) * b * b) := by
      simp [Matrix.det_mul, hdδ]
    have hinn := inn_torus Ψ a b o (Matrix.of h) t
    have hbound := (hC₁ (rt o (Ψ : E5 → ℂ)) B (hB o ho).1 (hB o ho).2
      (Matrix.of.symm (Matrix.of h * δ)) ((a : ℂ) * b * t) a b
      (by rw [hdh]; exact mul_ne_zero hdet (mul_ne_zero (mul_ne_zero ha hb) hb))
      (mul_ne_zero (mul_ne_zero ha hb) ht) ha)
    set I := ‖innB (rt o (Ψ : E5 → ℂ)) (Matrix.of.symm (Matrix.of h * δ)) ((a : ℂ) * b * t) a b‖ with hIdef
    set J := jm N (Matrix.of.symm (Matrix.of h * δ)) ((a : ℂ) * b * t) a b with hJ
    have hJ0 : 0 ≤ J := jm_nonneg _ _ _ _ _
    have hIJ : I ≤ |C₁ * B| * J :=
      hbound.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hJ0)
    have hnorm : ‖secI k Ψ g (h, t)‖ = ‖(a : ℂ)‖ ^ 4 * ‖(b : ℂ)‖ ^ 4 * I * (‖(Matrix.of h).det‖ ^ 2)⁻¹ := by
      have hr : ‖(Matrix.of h).det‖ ^ (-(2 : ℝ)) = (‖(Matrix.of h).det‖ ^ 2)⁻¹ := by
        rw [Real.rpow_neg hdet'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [secI]
      rw [norm_mul, norm_mul, norm_mul, norm_ph _ _ ht, norm_ph _ _ hdet, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), hr, show inn Ψ g (Matrix.of h) t = _ from hinn, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      ring
    have hGLv : GL' (h, t) = ((‖(Matrix.of h).det‖ * (‖(a : ℂ)‖ * ‖(b : ℂ)‖ * ‖(b : ℂ)‖)) ^ 2)⁻¹ * J := by
      simp only [hGL', hG]
      rw [hdh]
      simp only [norm_mul]
      rfl
    rw [hnorm, hGLv]
    have hfin : (‖(a : ℂ)‖ ^ 6 * ‖(b : ℂ)‖ ^ 8 * |C₁ * B|) *
        (((‖(Matrix.of h).det‖ * (‖(a : ℂ)‖ * ‖(b : ℂ)‖ * ‖(b : ℂ)‖)) ^ 2)⁻¹ * J) =
        ‖(a : ℂ)‖ ^ 4 * ‖(b : ℂ)‖ ^ 4 * (|C₁ * B| * J) * (‖(Matrix.of h).det‖ ^ 2)⁻¹ := by
      field_simp
    rw [hfin]
    gcongr
  have hint : ∫ p, ‖secI k Ψ g p‖ ≤ (‖(a : ℂ)‖ ^ 6 * ‖(b : ℂ)‖ ^ 8 * |C₁ * B|) * ∫ p, GL' p := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hGLi.const_mul _) (Filter.Eventually.of_forall hpt)
  have hsec : ‖sec k Ψ g‖ ≤ ‖(a : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ 4 * ∫ p, ‖secI k Ψ g p‖ := by
    rw [hF k hk Ψ g, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), det_g a b o ho]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have hGLe' : ∫ p, GL' p = (‖(a : ℂ)‖ ^ 6 * ‖(b : ℂ)‖ ^ 10)⁻¹ * ∫ p, G p := by
    rw [show (∫ p, GL' p) = _ from hGLe]
    congr 1
    simp only [norm_mul]
    ring_nf
  have hpowa : ‖(a : ℂ)‖ ^ (2 - ε) = ‖(a : ℂ)‖ ^ 2 * ‖(a : ℂ)‖ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha', show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpowb : ‖(b : ℂ)‖ ^ (2 - ε) = ‖(b : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hb', show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hmul : (‖(a : ℂ)‖ * ‖(b : ℂ)‖) ^ (-ε) = ‖(a : ℂ)‖ ^ (-ε) * ‖(b : ℂ)‖ ^ (-ε) :=
    Real.mul_rpow ha'.le hb'.le
  calc ‖sec k Ψ g‖ ≤ ‖(a : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ 4 * ∫ p, ‖secI k Ψ g p‖ := hsec
    _ ≤ ‖(a : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ 4 * ((‖(a : ℂ)‖ ^ 6 * ‖(b : ℂ)‖ ^ 8 * |C₁ * B|) * ∫ p, GL' p) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ‖(a : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ 2 * |C₁ * B| * ∫ p, G p := by
        rw [hGLe']
        field_simp
    _ ≤ ‖(a : ℂ)‖ ^ 2 * ‖(b : ℂ)‖ ^ 2 * |C₁ * B| * (C₂ * (‖(a : ℂ)‖ * ‖(b : ℂ)‖) ^ (-ε)) :=
        mul_le_mul_of_nonneg_left hGle (by positivity)
    _ = |C₁ * B| * C₂ * ‖(a : ℂ)‖ ^ (2 - ε) * ‖(b : ℂ)‖ ^ (2 - ε) := by
        rw [hpowa, hpowb, hmul]
        ring

end GlobalTheory.CompanionTheory.SecToC
