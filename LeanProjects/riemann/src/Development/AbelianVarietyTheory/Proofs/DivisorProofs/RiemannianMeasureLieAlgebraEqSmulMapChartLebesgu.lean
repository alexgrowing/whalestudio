import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.NormDetStrongContragredientDomRestrictAnnihilato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLieAlgebraEntriesOrthonormalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyInnerReEqStrictLowerAddDiagImStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyEqOfStrictLowerOfDiagImStatement

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section
namespace GlobalTheory.RiemConst.Jac

theorem addHaar_eq_gram {ι ι' F G : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
    (b : OrthonormalBasis ι' ℝ G) (e : Module.Basis ι ℝ F) (T : F ≃ₗ[ℝ] G) :
    b.toBasis.addHaar = ENNReal.ofReal (Real.sqrt (Matrix.of fun i j =>
      (inner ℝ (T (e i)) (T (e j)) : ℝ)).det) • e.addHaar.map T := by
  have hcard : Fintype.card ι' = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b.toBasis, ← Module.finrank_eq_card_basis e, T.finrank_eq]
  let b' := b.reindex (Fintype.equivOfCardEq hcard)
  let c := e.map T
  have h1 : b.toBasis.addHaar = b'.toBasis.addHaar := by
    rw [OrthonormalBasis.addHaar_eq_volume, OrthonormalBasis.addHaar_eq_volume]
  have h2 : b'.toBasis.addHaar = ENNReal.ofReal |b'.toBasis.det c| • c.addHaar := by
    conv_lhs => rw [Measure.addHaarMeasure_unique b'.toBasis.addHaar c.parallelepiped]
    rw [← Module.Basis.addHaar_def, ← Measure.addHaar_parallelepiped]
    rfl
  have h3 : c.addHaar = e.addHaar.map T := (Module.Basis.map_addHaar e T.toContinuousLinearEquiv).symm
  have h4 : |b'.toBasis.det c| = Real.sqrt (Matrix.of fun i j => (inner ℝ (T (e i)) (T (e j)) : ℝ)).det := by
    have := GlobalTheory.gramVol_eq_norm_det (𝕜 := ℝ) b' c
    have hg : Matrix.gram ℝ c = Matrix.of fun i j => (inner ℝ (T (e i)) (T (e j)) : ℝ) := by
      ext i j; simp [Matrix.gram, c]
    rw [Module.Basis.det_apply, ← Real.norm_eq_abs, ← this, GlobalTheory.gramVol, hg, RCLike.re_to_real]
  rw [h1, h2, h3, h4]

open scoped ComplexConjugate

theorem skew_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (hx : IsOrth X x) (Y : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r))
    (hY : fromFrame x Y ∈ realLie X.Ψ X.Gm) :
    (∀ τ a b, Y (τ, b, a) = -((sgn X.p0 a * sgn X.p0 b : ℝ) : ℂ) * conj (Y (τ, a, b))) ∧
      ∀ τ, ∑ a, Y (τ, a, a) = 0 := GlobalTheory.T.specialUnitaryLieAlgebra_entries_orthonormal_frame X x hx Y hY

theorem re_inner_skew {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, s a * s a = 1)
    (Y Y' : ι × Fin r × Fin r → ℂ)
    (hY : ∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b)))
    (hY' : ∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) :
    ∑ p, (conj (Y p) * Y' p).re =
      2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1},
        (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re +
      ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := GlobalTheory.T.skew_family_inner_re_eq_strictLower_add_diagIm s hs Y Y' hY hY'

theorem eq_of_skew {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, s a * s a = 1)
    (Y Y' : ι × Fin r × Fin r → ℂ)
    (hY : ∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b)))
    (htY : ∀ τ, ∑ a, Y (τ, a, a) = 0)
    (hY' : ∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b)))
    (htY' : ∀ τ, ∑ a, Y' (τ, a, a) = 0)
    (hlow : ∀ τ a b, b < a → Y (τ, a, b) = Y' (τ, a, b))
    (hdiag : ∀ τ (a : Fin r), (a : ℕ) + 1 < r → (Y (τ, a, a)).im = (Y' (τ, a, a)).im) : Y = Y' :=
  GlobalTheory.T.skew_family_eq_of_strictLower_of_diagIm s hs Y Y' hY htY hY' htY' hlow hdiag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem det_mat_ne (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h
  have e := congrArg Matrix.det (hx τ)
  rw [gram_eq, det_mul, det_mul, det_transpose, h, zero_mul, zero_mul, det_diagonal] at e
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) e.symm
  unfold sgn; split_ifs <;> norm_num

def frameL {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) where
  toFun Z := WithLp.toLp 2 fun p => inFrame x Z p.1 p.2.1 p.2.2
  map_add' Z Z' := by
    ext p
    have e : Matrix.of ((Z + Z') p.1) = Matrix.of (Z p.1) + Matrix.of (Z' p.1) := rfl
    simp only [inFrame, PiLp.toLp_apply, PiLp.add_apply, e, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c Z := by
    ext p
    have e : Matrix.of ((c • Z) p.1) = (c : ℂ) • Matrix.of (Z p.1) := rfl
    simp only [inFrame, PiLp.toLp_apply, PiLp.smul_apply, e, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply]
    rfl

theorem frameL_apply {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (Z : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) (a b : Fin r) :
    frameL x Z (τ, a, b) = inFrame x Z τ a b := rfl

theorem fromFrame_frameL (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (Z : X.Ψ → Fin r → Fin r → ℂ) :
    fromFrame x (frameL x Z) = Z := by
  funext τ
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (det_mat_ne X x hx τ)
  have e : Matrix.of (fun a b => (frameL x Z) (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (Z τ) * mat x τ := by
    ext a b; rfl
  change (mat x τ * Matrix.of (fun a b => (frameL x Z) (τ, a, b)) * (mat x τ)⁻¹ : Matrix _ _ ℂ) = Matrix.of (Z τ)
  rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem sum_angles_mul (hr : 1 ≤ r) (θ θ' : Fin (r - 1) → ℝ) :
    ∑ a : Fin r, angles θ a * angles θ' a = ∑ k, θ k * θ' k + (∑ k, θ k) * ∑ k, θ' k := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  simp [angles]

theorem gram_angles {r : ℕ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (hr : 1 ≤ r) (τ τ' : Ψ) (k k' : Fin (r - 1))
    (f g : Ψ → Fin (r - 1) → ℝ) (hf : ∀ σ j, f σ j = if (σ, j) = (τ, k) then 1 else 0)
    (hg : ∀ σ j, g σ j = if (σ, j) = (τ', k') then 1 else 0) :
    ∑ σ, ∑ a : Fin r, angles (f σ) a * angles (g σ) a = (1 : Matrix Ψ Ψ ℝ) τ τ' *
      (1 + Matrix.replicateCol Unit (fun _ : Fin (r - 1) => (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin (r - 1) => (1 : ℝ)) : Matrix (Fin (r - 1)) (Fin (r - 1)) ℝ) k k' := by
  simp only [sum_angles_mul hr, hf, hg, Prod.mk.injEq, ite_and]
  by_cases hτ : τ = τ'
  · subst hτ
    by_cases hk : k = k'
    · subst hk; simp [Finset.sum_add_distrib, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    · simp [Finset.sum_add_distrib, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, hk, Ne.symm hk]
  · simp [Finset.sum_add_distrib, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, hτ, Ne.symm hτ]

theorem angles_zero (a : Fin r) : angles (0 : Fin (r - 1) → ℝ) a = 0 := by
  unfold angles; split_ifs <;> simp

theorem measurePreserving_curry_real (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) volume volume := by
  have h : (volume : Measure (ι × κ → ℝ)) =
      (volume : Measure (ι → κ → ℝ)).map (MeasurableEquiv.curry ι κ ℝ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

theorem riemLie_eq_smul_map (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (hr : 1 ≤ r) (hx : IsOrth X x) (D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ))
    (hD : ∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧
      (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧
      ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ)) :
    Function.Injective D ∧ riemLie X.Ψ X.Gm x =
      ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) • (volume : Measure (ChartSp X)).map D := by
  classical
  have hinj : Function.Injective D := by
    intro w w' h
    have h1 : w.1 = w'.1 := by
      ext j
      obtain ⟨⟨τ, ⟨⟨a, b⟩, hab⟩⟩, rfl⟩ := (Fintype.equivFin (Ent X)).surjective j
      have := (hD w).2.1 τ a b hab
      rw [h, (hD w').2.1 τ a b hab] at this
      simpa [nmat, hab] using this.symm
    have h2 : w.2 = w'.2 := by
      funext τ k
      have := (hD w).2.2 τ ⟨k, by omega⟩
      rw [h, (hD w').2.2] at this
      have := Complex.ofReal_injective (mul_left_cancel₀ Complex.I_ne_zero this)
      simpa [angles] using this.symm
    exact Prod.ext h1 h2
  refine ⟨hinj, ?_⟩
  set s : Fin r → ℝ := fun a => sgn X.p0 a with hs_def
  have hs : ∀ a, s a * s a = 1 := fun a => by simp only [hs_def, sgn]; split_ifs <;> norm_num
  have hfv := fromFrame_frameL X x hx
  set S := (realLie X.Ψ X.Gm).comap (fromFrame x) with hS
  have hmem : ∀ w, frameL x (D w) ∈ S := fun w => by
    rw [hS, Submodule.mem_comap, hfv]; exact (hD w).1
  let T0 : ChartSp X →ₗ[ℝ] S := (frameL x ∘ₗ D.toLinearMap).codRestrict S hmem
  have hT0 : ∀ w, (T0 w : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r)) = frameL x (D w) := fun w => rfl
  have hskw : ∀ w, (∀ τ a b, frameL x (D w) (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (frameL x (D w) (τ, a, b))) ∧
      ∀ τ, ∑ a, frameL x (D w) (τ, a, a) = 0 := fun w =>
    skew_of_mem X x hx _ (by rw [hfv]; exact (hD w).1)
  have hT0inj : Function.Injective T0 := by
    intro w w' h
    apply hinj
    have := congrArg (fun Y : S => fromFrame x Y.1) h
    simpa only [hT0, hfv] using this
  have hT0surj : Function.Surjective T0 := by
    intro Y
    have hY := skew_of_mem X x hx Y.1 Y.2
    let w : ChartSp X := (WithLp.toLp 2 fun j => Y.1 (((Fintype.equivFin (Ent X)).symm j).1,
        ((Fintype.equivFin (Ent X)).symm j).2.1.1, ((Fintype.equivFin (Ent X)).symm j).2.1.2),
      fun τ k => (Y.1 (τ, ⟨k, by omega⟩, ⟨k, by omega⟩)).im)
    refine ⟨w, Subtype.ext ?_⟩
    rw [hT0]
    have key := eq_of_skew s hs (fun p => frameL x (D w) p) (fun p => Y.1 p) (hskw w).1 (hskw w).2 hY.1 hY.2
      (fun τ a b hab => by
        simp only [frameL_apply, (hD w).2.1 τ a b hab, nmat, dif_pos hab, w, PiLp.toLp_apply, Equiv.symm_apply_apply])
      (fun τ a ha => by
        simp only [frameL_apply, (hD w).2.2 τ a, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, zero_add, angles, dif_pos (show (a : ℕ) < r - 1 by omega), w])
    ext p
    exact congrFun key p
  let T : ChartSp X ≃ₗ[ℝ] S := LinearEquiv.ofBijective T0 ⟨hT0inj, hT0surj⟩
  have hTw : ∀ w, ((T w : S) : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r)) = frameL x (D w) := fun w => rfl

  have hinner : ∀ w w' : ChartSp X, (inner ℝ (T w) (T w') : ℝ) =
      2 * (inner ℝ w.1 w'.1 : ℝ) + ∑ τ, ∑ a, angles (w.2 τ) a * angles (w'.2 τ) a := by
    intro w w'
    rw [Submodule.coe_inner, hTw, hTw, PiLp.inner_apply, PiLp.inner_apply]
    simp only [Complex.inner]
    have hre := re_inner_skew s hs (fun p => frameL x (D w) p) (fun p => frameL x (D w') p) (hskw w).1 (hskw w').1
    have hlow : ∀ (v : ChartSp X) (q : Ent X), frameL x (D v) (q.1, q.2.1.1, q.2.1.2) =
        v.1 (Fintype.equivFin (Ent X) q) := by
      intro v q
      rw [frameL_apply, (hD v).2.1 _ _ _ q.2.2]
      simp only [nmat, dif_pos q.2.2]
    have hdg : ∀ (v : ChartSp X) τ a, (frameL x (D v) (τ, a, a)).im = angles (v.2 τ) a := by
      intro v τ a
      rw [frameL_apply, (hD v).2.2]; simp
    calc _ = ∑ p, (conj (frameL x (D w) p) * frameL x (D w') p).re :=
          Finset.sum_congr rfl fun p _ => by rw [mul_comm]
      _ = _ := hre
      _ = _ := by
          simp only [hlow, hdg]
          congr 2
          exact (Equiv.sum_comp (Fintype.equivFin (Ent X)) (fun j => (conj (w.1 j) * w'.1 j).re)).trans
            (Finset.sum_congr rfl fun j _ => by rw [mul_comm])

  let b1 := stdOrthonormalBasis ℝ (V (nd X))
  let b2 : Module.Basis (X.Ψ × Fin (r - 1)) ℝ (X.Ψ → Fin (r - 1) → ℝ) :=
    (Pi.basisFun ℝ (X.Ψ × Fin (r - 1))).map (LinearEquiv.curry ℝ ℝ X.Ψ (Fin (r - 1)))
  let e := b1.toBasis.prod b2
  have hb2 : ∀ p τ k, b2 p τ k = if (τ, k) = p then 1 else 0 := by
    intro p τ k; simp [b2, Pi.single_apply]
  have hvol2 : b2.addHaar = volume := by
    have h1 := Module.Basis.map_addHaar (Pi.basisFun ℝ (X.Ψ × Fin (r - 1)))
      (LinearEquiv.curry ℝ ℝ X.Ψ (Fin (r - 1))).toContinuousLinearEquiv
    have h2 : (Pi.basisFun ℝ (X.Ψ × Fin (r - 1))).addHaar = volume := by
      rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]
    rw [h2] at h1
    have h3 : b2.addHaar = Measure.map (LinearEquiv.curry ℝ ℝ X.Ψ (Fin (r - 1))).toContinuousLinearEquiv volume :=
      h1.symm
    rw [h3]
    exact (measurePreserving_curry_real X.Ψ (Fin (r - 1))).map_eq
  have hvol : e.addHaar = (volume : Measure (ChartSp X)) := by
    rw [Module.Basis.prod_addHaar, OrthonormalBasis.addHaar_eq_volume, hvol2]; rfl
  have hgram : (Matrix.of fun i j => (inner ℝ (T (e i)) (T (e j)) : ℝ)) =
      Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix _ _ ℝ)) 0 0
        (Matrix.kroneckerMap (· * ·) (1 : Matrix X.Ψ X.Ψ ℝ)
          (1 + Matrix.replicateCol Unit (fun _ : Fin (r - 1) => (1 : ℝ)) *
            Matrix.replicateRow Unit (fun _ : Fin (r - 1) => (1 : ℝ)))) := by
    have he1 : ∀ i, e (Sum.inl i) = (b1 i, 0) := fun i => by simp [e]
    have he2 : ∀ p, e (Sum.inr p) = (0, b2 p) := fun p => by simp [e]
    have hon := orthonormal_iff_ite.mp b1.orthonormal
    ext i j
    rcases i with i | ⟨τ, k⟩ <;> rcases j with j | ⟨τ', k'⟩
    · simp only [Matrix.of_apply, hinner, he1, Pi.zero_apply, angles_zero, mul_zero, Finset.sum_const_zero,
        add_zero, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply, hon, smul_eq_mul]
    · simp [hinner, he1, he2, angles_zero]
    · simp [hinner, he1, he2, angles_zero]
    · simp only [Matrix.of_apply, hinner, he2, inner_zero_left, mul_zero, zero_add, Matrix.fromBlocks_apply₂₂]
      rw [Matrix.kroneckerMap_apply]
      exact gram_angles hr τ τ' k k' _ _ (hb2 _) (hb2 _)
  have hdet : (Matrix.of fun i j => (inner ℝ (T (e i)) (T (e j)) : ℝ)).det =
      2 ^ (2 * nd X) * (r : ℝ) ^ X.Ψ.card := by
    rw [hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_kronecker, Matrix.det_one_add_replicateCol_mul_replicateRow]
    have hfr : Module.finrank ℝ (V (nd X)) = 2 * nd X := by
      rw [← Module.finrank_mul_finrank ℝ ℂ]; simp
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hfr, Matrix.det_one, one_pow, one_mul,
      Fintype.card_coe]
    congr 2
    simp [dotProduct, Nat.cast_sub hr]
  have hK : Real.sqrt (2 ^ (2 * nd X) * (r : ℝ) ^ X.Ψ.card) = 2 ^ nd X * Real.sqrt r ^ X.Ψ.card := by
    have h1 : (2 : ℝ) ^ (2 * nd X) = (2 ^ nd X) ^ 2 := by rw [← pow_mul, mul_comm]
    have h2 : (r : ℝ) ^ X.Ψ.card = (Real.sqrt r ^ X.Ψ.card) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg r)]
    rw [h1, h2, ← mul_pow, Real.sqrt_sq (by positivity)]
  have hmeasT : Measurable (fun w : ChartSp X => T w) :=
    (LinearMap.continuous_of_finiteDimensional (T : ChartSp X →ₗ[ℝ] S)).measurable
  have hf : Measurable (fun Y : S => fromFrame x Y.1) :=
    ((LinearMap.continuous_of_finiteDimensional (fromFrame x)).comp continuous_subtype_val).measurable
  show Measure.map (fun Y : S => fromFrame x Y.1) (stdOrthonormalBasis ℝ S).toBasis.addHaar = _
  rw [addHaar_eq_gram (stdOrthonormalBasis ℝ S) e T, hdet, hK, Measure.map_smul, Measure.map_map hf hmeasT, hvol]
  congr 2
  funext w
  exact hfv (D w)

end GlobalTheory.RiemConst.Jac
