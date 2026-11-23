import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap

noncomputable section

namespace GlobalTheory.SUVol.LieMeas

open MeasureTheory Matrix
open scoped ENNReal

theorem det_gram_eq_sq {ι W : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (o : OrthonormalBasis ι ℝ W) (b : ι → W) :
    (Matrix.of fun p q => inner ℝ (b p) (b q)).det = (o.toBasis.det b) ^ 2 := by
  have h : (Matrix.of fun p q => inner ℝ (b p) (b q)) = (o.toBasis.toMatrix b)ᵀ * o.toBasis.toMatrix b := by
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rw [← o.sum_inner_mul_inner]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]
  rw [h, det_mul, det_transpose, Module.Basis.det_apply, sq]

theorem volume_eq_sqrt_gram {ι W : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (b : Module.Basis ι ℝ W) :
    (stdOrthonormalBasis ℝ W).toBasis.addHaar =
      ENNReal.ofReal (Real.sqrt |(Matrix.of fun p q => inner ℝ (b p) (b q)).det|) • b.addHaar := by
  let e : Fin (Module.finrank ℝ W) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b])
  let o : OrthonormalBasis ι ℝ W := (stdOrthonormalBasis ℝ W).reindex e
  have ho : (stdOrthonormalBasis ℝ W).toBasis.addHaar = o.toBasis.addHaar := by
    rw [OrthonormalBasis.addHaar_eq_volume, OrthonormalBasis.addHaar_eq_volume]
  rw [ho, det_gram_eq_sq o, abs_sq, Real.sqrt_sq_eq_abs, ← Measure.addHaar_parallelepiped]
  have := Measure.addHaarMeasure_unique o.toBasis.addHaar b.parallelepiped
  rw [← Module.Basis.addHaar_def] at this
  exact this

theorem volume_eq_sqrt_gram_map {ι κ W : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (f : (ι → κ → ℝ) ≃ₗ[ℝ] W) :
    (stdOrthonormalBasis ℝ W).toBasis.addHaar =
      ENNReal.ofReal (Real.sqrt |(Matrix.of fun p q : κ × ι => inner ℝ (f (Pi.single p.2 (Pi.single p.1 1)))
        (f (Pi.single q.2 (Pi.single q.1 1)))).det|) • Measure.map f volume := by
  let u : (ι → κ → ℝ) ≃ₗ[ℝ] (κ × ι → ℝ) :=
    { toFun := fun c p => c p.2 p.1, invFun := fun c t i => c (i, t), map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let b : Module.Basis (κ × ι) ℝ W := Module.Basis.ofEquivFun (f.symm.trans u)
  have hb : ∀ p, b p = f (Pi.single p.2 (Pi.single p.1 1)) := by
    intro p
    rw [Module.Basis.coe_ofEquivFun]
    simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
    congr 1
    funext t i
    change Pi.single (M := fun _ => ℝ) p 1 (i, t) = _
    obtain ⟨j, s⟩ := p
    by_cases h : t = s
    · subst h; simp [Pi.single_apply]
    · simp [Pi.single_apply, h]
  have hcont : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  have : (Measure.map f volume).IsAddHaarMeasure := f.toContinuousLinearEquiv.isAddHaarMeasure_map volume
  have hm : b.addHaar = Measure.map f volume := by
    rw [Module.Basis.addHaar_eq_iff, Measure.map_apply hcont.measurable
      b.parallelepiped.isCompact.measurableSet]
    have : f ⁻¹' (b.parallelepiped : Set W) = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1 := by
      ext c
      rw [Module.Basis.coe_parallelepiped, parallelepiped_basis_eq]
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
      have hr : ∀ p, b.repr (f c) p = c p.2 p.1 := by
        intro p
        rw [Module.Basis.ofEquivFun_repr_apply]
        simp [u]
      simp only [hr]
      exact ⟨fun h t i => h (i, t), fun h p => h _ _⟩
    rw [this]
    simp only [volume_pi_pi, Real.volume_Icc]
    simp
  rw [volume_eq_sqrt_gram b, hm]
  simp only [hb]

theorem abs_det_re_trace {r : ℕ} (D : Matrix (Fin r) (Fin r) ℂ) (hD : D * D = 1)
    (hDc : D.map (starRingEnd ℂ) = D)
    (Y : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ) (hli : LinearIndependent ℝ Y)
    (hY : ∀ i, (Y i)ᵀ * D + D * (Y i).map (starRingEnd ℂ) = 0 ∧ (Y i).trace = 0) :
    |(Matrix.of fun i j => (trace (Y i * (Y j)ᴴ)).re).det| =
      ‖(Matrix.of fun i j => trace (Y i * Y j)).det‖ := by
  have hdet : D.det ≠ 0 := by
    intro h; have := congrArg Matrix.det hD; simp [h] at this
  have hH : ∀ i, (Y i)ᴴ = -(D * Y i * D) := by
    intro i
    have h1 : (Y i)ᵀ = -(D * (Y i).map (starRingEnd ℂ) * D) := by
      rw [← neg_mul, ← eq_neg_of_add_eq_zero_left (hY i).1, Matrix.mul_assoc, hD, Matrix.mul_one]
    have h2 : (Y i)ᴴ = ((Y i)ᵀ).map (starRingEnd ℂ) := rfl
    rw [h2, h1, Matrix.map_neg _ (map_neg _), Matrix.map_mul, Matrix.map_mul, hDc]
    congr 3
    ext a b; simp
  have hspan : ∀ j, (Y j)ᴴ ∈ Submodule.span ℝ (Set.range Y) := by
    intro j
    refine GlobalTheory.T.unitary_lie_algebra_spanned D hdet Y hli hY _ ?_ (by rw [trace_conjTranspose, (hY j).2, star_zero])
    have e1 : ((Y j)ᴴ)ᵀ = (Y j).map (starRingEnd ℂ) := rfl
    have e2 : ((Y j)ᴴ).map (starRingEnd ℂ) = (Y j)ᵀ := by ext a b; simp
    have := congrArg (fun M => D * M * D) (hY j).1
    simp only [mul_add, add_mul, mul_zero, zero_mul, ← Matrix.mul_assoc, hD, Matrix.one_mul] at this
    rw [Matrix.mul_assoc _ D D, hD, Matrix.mul_one] at this
    rw [e1, e2, add_comm, this]
  choose θ hθ using fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan j)
  have hsq : Matrix.of θ * Matrix.of θ = 1 := by
    ext j k
    have h1 : Y j = ∑ k, (Matrix.of θ * Matrix.of θ) j k • Y k := by
      conv_lhs => rw [← conjTranspose_conjTranspose (Y j), ← hθ j, conjTranspose_sum]
      simp only [conjTranspose_smul, star_trivial, ← hθ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
        Finset.sum_smul, Matrix.of_apply]
      exact Finset.sum_comm
    have h2 : ∑ k, ((Matrix.of θ * Matrix.of θ) j k - (1 : Matrix _ _ ℝ) j k) • Y k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← h1]
      simp [Matrix.one_apply]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 k)
  have hreal : ∀ i j, ((trace (Y i * Y j)).re : ℂ) = trace (Y i * Y j) := by
    intro i j
    refine Complex.conj_eq_iff_re.1 ?_
    change star _ = _
    rw [← trace_conjTranspose, conjTranspose_mul, hH, hH, neg_mul_neg]
    calc _ = trace (D * (Y j * (D * D) * Y i * D)) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [trace_mul_comm, hD, Matrix.mul_one, Matrix.mul_assoc, hD, Matrix.mul_one, trace_mul_comm]
  have hB : (Matrix.of fun i j => trace (Y i * Y j)) =
      (Matrix.of fun i j => (trace (Y i * Y j)).re).map Complex.ofRealHom := by
    ext i j; exact (hreal i j).symm
  have hM : (Matrix.of fun i j => (trace (Y i * (Y j)ᴴ)).re) =
      (Matrix.of fun i j => (trace (Y i * Y j)).re) * (Matrix.of θ)ᵀ := by
    ext i j
    rw [Matrix.of_apply, ← hθ j]
    simp [Matrix.mul_apply, Finset.mul_sum, trace_sum, mul_comm]
  have habs : |(Matrix.of θ).det| = 1 := by
    have h2 : |(Matrix.of θ).det| * |(Matrix.of θ).det| = 1 := by rw [← abs_mul, ← det_mul, hsq, det_one, abs_one]
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · have := abs_nonneg (Matrix.of θ).det; linarith
  rw [hM, det_mul, det_transpose, abs_mul, habs, mul_one, hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp

section Main

open NumberField GlobalTheory.SUVol GlobalTheory.SUVol.DensOne ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def toFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) where
  toFun X := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X p.1) * mat x p.1) p.2.1 p.2.2)
  map_add' X Y := by
    refine PiLp.ext fun p => ?_
    have e : Matrix.of ((X + Y) p.1) = Matrix.of (X p.1) + Matrix.of (Y p.1) := rfl
    simp only [PiLp.add_apply, e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c X := by
    refine PiLp.ext fun p => ?_
    have e : Matrix.of ((c • X) p.1) = c • Matrix.of (X p.1) := rfl
    simp only [PiLp.smul_apply, e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply]

omit [NumberField E] [IsCMField E] in
theorem toFrame_apply {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (X : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Matrix.of (fun a b => toFrame x X (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ := rfl

theorem fromFrame_toFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0)
    (X : Ψ → Fin r → Fin r → ℂ) : fromFrame x (toFrame x X) = X := by
  funext τ
  change (mat x τ * Matrix.of (fun a b => toFrame x X (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X τ
  rw [toFrame_apply, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  rfl

theorem toFrame_fromFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0)
    (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) : toFrame x (fromFrame x Y) = Y := by
  refine PiLp.ext fun p => ?_
  obtain ⟨τ, a, b⟩ := p
  have h : Matrix.of (fun a b => toFrame x (fromFrame x Y) (τ, a, b)) = Matrix.of (fun a b => Y (τ, a, b)) := by
    rw [toFrame_apply]
    change (mat x τ)⁻¹ * (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹) * mat x τ = _
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  exact congrFun (congrFun h a) b

theorem inner_eq_sum_trace {ι : Type} [Fintype ι] (Y Z : EuclideanSpace ℂ (ι × Fin r × Fin r)) :
    inner ℝ Y Z = ∑ τ, (trace (Matrix.of (fun a b => Y (τ, a, b)) * (Matrix.of (fun a b => Z (τ, a, b)))ᴴ)).re := by
  rw [PiLp.inner_apply]
  simp [Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply, Complex.inner, mul_comm]

omit [NumberField E] [IsCMField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem riemLie_eq_smul_formLie (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (_hr : 2 ≤ r) (ho : IsOrth X x)
    (he : ∀ i, (e i).trace = 0 ∧ ∀ u w, herm X.Gm (e i *ᵥ u) w + herm X.Gm u (e i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) e) :
    riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt
      ‖∏ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie X.Ψ e := by
  classical
  have hG := X.Gm_det
  set G := X.Gm with hGdef
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hDdef
  have hD : D * D = 1 := by
    rw [hDdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext a; unfold sgn; split_ifs <;> simp
  have hDc : D.map (starRingEnd ℂ) = D := by
    rw [hDdef, diagonal_map (map_zero _)]
    congr 1; funext a; simp
  have hxD : ∀ τ, (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) = D := fun τ => by
    rw [← gram_eq]; exact ho τ
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ h
    have h1 := congrArg Matrix.det (hxD τ)
    have h2 := congrArg Matrix.det hD
    rw [det_mul, det_mul, det_transpose, h] at h1
    simp [← h1] at h2
  have hsk : ∀ i, (e i)ᵀ * G + G * (e i).map cc = 0 := fun i => skew_matrix G (he i).2
  have hE : LinearIndependent E e := GlobalTheory.T.real_independent_skew_matrices G hG e hsk hli
  have hR : ∀ τ : X.Ψ, LinearIndependent ℝ (fun i => (e i).map τ.1) := fun τ => GlobalTheory.T.linear_independent_complex_map τ.1 e hE
  have hmem : ∀ (τ : X.Ψ) i, ((e i).map τ.1)ᵀ * G.map τ.1 + G.map τ.1 * ((e i).map τ.1).map (starRingEnd ℂ) = 0 ∧
      ((e i).map τ.1).trace = 0 := by
    intro τ i
    refine ⟨map_skew G (hsk i) τ.1, ?_⟩
    have h1 : ((e i).map τ.1).trace = τ.1 (e i).trace := by simp [Matrix.trace, map_sum]
    rw [h1, (he i).1, map_zero]
  have hinj : Function.Injective (coordMap X.Ψ e) := by
    refine (injective_iff_map_eq_zero (coordMap X.Ψ e)).2 fun c hc => funext fun τ => funext fun i => ?_
    have h1 := coordMap_apply X.Ψ e c τ
    rw [hc] at h1
    exact Fintype.linearIndependent_iff.1 (hR τ) (c τ) h1.symm i
  have hsurj : ∀ Z ∈ realLie X.Ψ G, ∃ c, coordMap X.Ψ e c = Z := by
    intro Z hZ
    have hX' := (mem_realLie_iff X.Ψ G Z).1 hZ
    have hspan : ∀ τ : X.Ψ, Matrix.of (Z τ) ∈ Submodule.span ℝ (Set.range fun i => (e i).map τ.1) :=
      fun τ => GlobalTheory.T.unitary_lie_algebra_spanned (G.map τ.1) (det_map_ne G hG τ.1) _ (hR τ) (hmem τ) _ (hX' τ).1 (hX' τ).2
    choose c hc using fun τ => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan τ)
    refine ⟨c, funext fun τ => ?_⟩
    have h1 := coordMap_apply X.Ψ e c τ
    rw [hc τ] at h1
    exact h1
  have hin : ∀ c, coordMap X.Ψ e c ∈ realLie X.Ψ G := by
    intro c
    refine (mem_realLie_iff X.Ψ G _).2 fun τ => ?_
    rw [coordMap_apply]
    refine ⟨?_, by simp [trace_sum, (hmem τ _).2]⟩
    have h1 : (∑ i, c τ i • (e i).map τ.1).map (starRingEnd ℂ) =
        ∑ i, c τ i • ((e i).map τ.1).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.sum_apply]
    rw [h1, transpose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hmem τ i).1, smul_zero]
  let f0 : (X.Ψ → Fin (r ^ 2 - 1) → ℝ) →ₗ[ℝ] (realLie X.Ψ G).comap (fromFrame x) :=
    ((toFrame x).comp (coordMap X.Ψ e)).codRestrict _ fun c => by
      change fromFrame x (toFrame x (coordMap X.Ψ e c)) ∈ realLie X.Ψ G
      rw [fromFrame_toFrame x hx]; exact hin c
  have hf0 : ∀ c, fromFrame x (f0 c).1 = coordMap X.Ψ e c := fun c => fromFrame_toFrame x hx _
  have hb : Function.Bijective f0 := by
    refine ⟨fun c d h => hinj (by rw [← hf0, ← hf0, h]), fun Y => ?_⟩
    obtain ⟨c, hc⟩ := hsurj _ Y.2
    refine ⟨c, Subtype.ext ?_⟩
    change toFrame x (coordMap X.Ψ e c) = Y.1
    rw [hc, toFrame_fromFrame x hx]
  let f := LinearEquiv.ofBijective f0 hb
  let Y : X.Ψ → Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ := fun τ i => (mat x τ)⁻¹ * (e i).map τ.1 * mat x τ
  have hfY : ∀ τ i σ, Matrix.of (fun a b => (f (Pi.single τ (Pi.single i 1))).1 (σ, a, b)) =
      if σ = τ then Y τ i else 0 := by
    intro τ i σ
    change Matrix.of (fun a b => toFrame x (coordMap X.Ψ e (Pi.single τ (Pi.single i 1))) (σ, a, b)) = _
    rw [toFrame_apply, coordMap_apply]
    split_ifs with h
    · subst h; simp [Y, Pi.single_apply]
    · simp [h]
  have hgram : (Matrix.of fun p q : Fin (r ^ 2 - 1) × X.Ψ => inner ℝ (f (Pi.single p.2 (Pi.single p.1 1)))
      (f (Pi.single q.2 (Pi.single q.1 1)))) =
      blockDiagonal fun τ => Matrix.of fun i j => (trace (Y τ i * (Y τ j)ᴴ)).re := by
    ext ⟨i, τ⟩ ⟨j, σ⟩
    rw [Matrix.of_apply, Submodule.coe_inner, inner_eq_sum_trace, blockDiagonal_apply]
    simp only [hfY]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]
  have hYli : ∀ τ, LinearIndependent ℝ (Y τ) := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun g hg => Fintype.linearIndependent_iff.1 (hR τ) g ?_
    have h1 : (mat x τ)⁻¹ * (∑ i, g i • (e i).map τ.1) * mat x τ = 0 := by
      rw [← hg]; simp [Y, Finset.mul_sum, Finset.sum_mul]
    have h2 := congrArg (fun M => mat x τ * M * (mat x τ)⁻¹) h1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h2
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit] at h2
  have htr : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ), trace ((mat x τ)⁻¹ * M * mat x τ) = trace M := by
    intro τ M
    rw [trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hYsk : ∀ τ i, (Y τ i)ᵀ * D + D * (Y τ i).map (starRingEnd ℂ) = 0 ∧ (Y τ i).trace = 0 := by
    intro τ i
    refine ⟨?_, by rw [htr, (hmem τ i).2]⟩
    have h0 : mat x τ * Y τ i = (e i).map τ.1 * mat x τ := by
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    have h1 := congrArg (fun M => (mat x τ)ᵀ * M * (mat x τ).map (starRingEnd ℂ)) (hmem τ i).1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
    rw [← hxD τ, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, h0, transpose_mul,
      Matrix.mul_assoc _ ((mat x τ).map _), ← Matrix.map_mul, h0, Matrix.map_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hdetτ : ∀ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      (Matrix.of fun i j => trace (Y τ i * Y τ j)).det := by
    intro τ
    rw [RingHom.map_det]
    congr 1
    ext i j
    have h1 : Y τ i * Y τ j = (mat x τ)⁻¹ * ((e i * e j).map τ.1) * mat x τ := by
      rw [Matrix.map_mul]
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    rw [Matrix.of_apply, h1, htr]
    simp [Matrix.trace, map_sum, Matrix.mul_apply]
  have hcF : Continuous fun Z : (realLie X.Ψ G).comap (fromFrame x) => fromFrame x Z.1 :=
    (fromFrame x).continuous_of_finiteDimensional.comp continuous_subtype_val
  have hcf : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  unfold riemLie
  rw [volume_eq_sqrt_gram_map f, Measure.map_smul, Measure.map_map hcF.measurable hcf.measurable, hgram,
    det_blockDiagonal, Finset.abs_prod, norm_prod]
  congr 3
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdetτ, abs_det_re_trace D hD hDc (Y τ) (hYli τ) (hYsk τ)]
  · funext c
    exact hf0 c

end Main

end GlobalTheory.SUVol.LieMeas
