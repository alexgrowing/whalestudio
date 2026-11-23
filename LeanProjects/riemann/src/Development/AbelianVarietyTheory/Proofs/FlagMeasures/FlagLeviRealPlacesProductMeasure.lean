import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplementaryBlockUnitaryFormsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstancesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFlagBlockFixingLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPosStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNullStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMoveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroupStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open Formalism.REAL (Jm UJ muG)

noncomputable section

namespace GlobalTheory.LeviIso

theorem detNorm_pos_iff {E : Type} [Field E] [NumberField E] {j : ℕ} (x : MatInf E j) :
    0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw]; simp)] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem gram_place (I : AutInst) (v : InfinitePlace I.F) {p q : Type} (X : Matrix (Fin I.n) p I.E)
    (Y : Matrix (Fin I.n) q I.E) :
    ((I.P v)⁻¹ * X.map (I.φ v))ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * Y.map (I.φ v)) = (Xᴴ * I.J * Y).map (I.φ v) := by
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hX : (X.map (I.φ v))ᴴ = Xᴴ.map (I.φ v) := by
    ext r s
    exact (I.cm.cmUnram.2.1 (I.φ v) (X s r)).symm
  rw [← I.P_spec v, Matrix.map_mul, Matrix.map_mul, ← hX]
  calc _ = (I.P v * (I.P v)⁻¹ * X.map (I.φ v))ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹ * Y.map (I.φ v)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.one_mul, Matrix.one_mul]

theorem conjT_map {τ : ℂ →+* ℂ} (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) {p q : Type} (X : Matrix p q ℂ) :
    (X.map τ)ᴴ = Xᴴ.map τ := by
  rcases hτ with rfl | rfl <;> ext r s <;> simp

theorem Jm_map {n : ℕ} (ε : Fin n → Bool) (τ : ℂ →+* ℂ) : (Jm ε).map τ = Jm ε := by
  ext r s
  simp only [Jm, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem inv_map {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (τ : ℂ →+* ℂ) :
    P.map τ * P⁻¹.map τ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
  simp

theorem exists_charts (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) (v : InfinitePlace I.F)
    (v₀ : InfinitePlace I₀.F) (τ τ₀ : ℂ →+* ℂ) (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ)
    (hτ₀ : τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) (hv : ∀ y, I.φ v (e y) = τ₀ (I₀.φ v₀ y)) :
    ∃ θ, IsLeviChart (I.ε v) (I₀.ε v₀) (flagAt I S v) (fun i => (I.P v)⁻¹ * (T i).map (I.φ v))
      ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P v₀).map τ₀) τ τ₀ θ := by
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  have hsp := GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis I I₀ e xf a j S Λ x₀ T T' T₀ h v
  obtain ⟨-, hn, -, h1, h2, h3, -, -⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  have sw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := by
    intro i k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  refine GlobalTheory.T.complementary_block_unitary_forms _ _ a j _ _ _ _ (fun i => ((I.P v)⁻¹ * (T' i).map (I.φ v))ᴴ * Jm (I.ε v)) _ τ τ₀ hτ hτ₀ hn
    (fun i => ?_) (fun i k hik => ?_) (fun i k => ?_) (fun i => ?_) ?_ hsp (GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag I _ a j S hsat v)
  · rw [gram_place, sw, (h2 i).1]
    simp
  · rw [gram_place, sw, (h1 k i).2.2 hik.symm]
    simp
  · rw [gram_place, (h1 i k).1]
    simp
  · rw [← Matrix.mul_assoc, gram_place, (h2 i).2.1]
    simp
  · have e1 : (I₀.J.map e).map (I.φ v) = (I₀.J.map (I₀.φ v₀)).map τ₀ := by
      ext r s
      exact hv _
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm _),
      ← Matrix.mul_assoc _ _ ((I₀.P v₀).map τ₀), ← Matrix.mul_assoc _ (Jm _), gram_place, h3, e1,
      conjT_map hτ₀, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, I₀.P_spec, Jm_map]

theorem size_solve {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) {s t D : ℝ} (hs : 0 < s) (ht : 0 < t) (hD : 0 < D)
    (h : t ^ f = s ^ f * D ^ (-(1 : ℝ) / (2 * k))) :
    t = (D / s ^ (2 * f * k)) ^ (-(1 / (2 * (f : ℝ) * k))) := by
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 := congrArg Real.log h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_rpow hD] at h1
  apply Real.log_injOn_pos ht (Real.rpow_pos_of_pos (by positivity) _)
  rw [Real.log_rpow (by positivity), Real.log_div hD.ne' (by positivity), Real.log_pow]
  push_cast
  field_simp
  field_simp at h1
  linarith

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] {a : ℕ} (j : Fin a → ℕ) :
    ∀ᵐ z ∂(Measure.pi fun i => haarGL E (j i)), ∀ i, 0 < detNorm E (j i) (z i) := by
  have hσ : ∀ i, SigmaFinite (haarGL E (j i)) := fun i => by
    rw [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    exact inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => haarLoc (j i)))
  have h1 : ∀ i, ∀ᵐ x ∂(haarGL E (j i)), 0 < detNorm E (j i) x := by
    intro i
    rw [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    have h2 : ∀ᵐ x ∂(Measure.pi fun _ : InfinitePlace E => haarLoc (j i)), ∀ w, (Matrix.of (x w)).det ≠ 0 := by
      refine ae_all_iff.2 fun w => ?_
      have h3 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
        rw [ae_iff]
        simpa using (GlobalTheory.T.haarComplexGLMatrices_conj_and_singular_null (j i)).2
      exact (Measure.quasiMeasurePreserving_eval (fun _ : InfinitePlace E => haarLoc (j i)) w).ae h3
    exact h2.mono fun x hx => (detNorm_pos_iff x).2 hx
  exact ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval (fun i => haarGL E (j i)) i).ae (h1 i)

theorem levi_product : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj h μM _ c₀ hμ hc₀
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  obtain ⟨β, σ, τ, τ₀, hτ, hτ₀, hβ, hσ⟩ := GlobalTheory.T.realPlaces_match_isomorphic_CM_instances I I₀ e h.1
  choose θ hθ using fun v => exists_charts I I₀ e xf a j S Λ x₀ T T' T₀ hj h v (σ v) (τ v) (τ₀ v) (hτ v) (hτ₀ v)
    (hσ v)
  have hcard : Fintype.card (InfinitePlace I.F) = I.f := GlobalTheory.Count.FrameMajorant.card_places I
  have hf : 1 ≤ I.f := Module.finrank_pos
  let R : (∀ i, MatInf I.E (j i)) × I₀.Ginf →
      ∀ v : InfinitePlace I.F, (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ (I₀.ε (σ v)) :=
    fun z v => (fun i => z.1 i (β v), z.2 (σ v))
  have hR := GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures _ _ _ β σ a (fun i => Fin (j i) → Fin (j i) → ℂ) (fun w => UJ (I₀.ε w))
    (fun i => haarLoc (j i)) (fun w => muG (I₀.ε w)) (fun i => 2 ^ (j i ^ 2)) c₀ (fun i => by positivity)
    (fun w => ((GlobalTheory.T.riemannianHaarGauge_whole_group _ _).1 _ (hc₀ w)).1.le)
  have hRm : Measurable R := hR.measurable
  have hΘ : Measurable fun (z : (∀ i, MatInf I.E (j i)) × I₀.Ginf) v => θ v (R z v) :=
    measurable_pi_lambda _ fun v => (hθ v).1.comp ((measurable_pi_apply v).comp hRm)
  have hdet : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v i, (Matrix.of ((R z v).1 i)).det ≠ 0 := fun z hz v i => (detNorm_pos_iff _).1 (hz i) (β v)
  have hM : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v, θ v (R z v) ∈ flagM (I.ε v) (flagAt I S v) := fun z hz v =>
    ((hθ v).2.1 _).2 ⟨R z v, hdet z hz v, rfl⟩
  have hpos := fun g : I.Ginf => GlobalTheory.T.sizeQ_saturatedIsotropicFlag_pos I (g, xf) a j S hsat
  refine ⟨fun z v => θ v (R z v), fun i => sizesAt I xf S 1 i ^ (2 * I.f * j i), hΘ,
    fun i => pow_pos (hpos 1 i) _, fun m => ⟨fun hm => ?_, ?_⟩, fun z z' hz1 hz2 hz' => ?_, fun z hz i => ?_,
    fun z z' hz hz' hzz => ?_, fun φ hφ => ?_⟩
  · choose y hy1 hy2 using fun v => ((hθ v).2.1 (m v)).1 (hm v)
    refine ⟨(fun i w => (y (β.symm w)).1 i, Equiv.piCongrLeft (fun w => UJ (I₀.ε w)) σ fun v => (y v).2),
      fun i => (detNorm_pos_iff _).2 fun w => hy1 _ i, funext fun v => ?_⟩
    rw [← hy2 v]
    refine congrArg (θ v) (Prod.ext (funext fun i => ?_) ?_)
    · exact congrArg (fun u => (y u).1 i) (β.symm_apply_apply v)
    · exact Equiv.piCongrLeft_apply_apply (fun w => UJ (I₀.ε w)) σ (fun v => (y v).2) v
  · rintro ⟨z, hz, rfl⟩
    exact hM z hz
  · choose γ hγ1 hγ2 using hz1
    obtain ⟨g, hg, Γ, γ₀, g1, g2, g3, g4⟩ := GlobalTheory.T.exists_rational_flag_block_fixing_lattice I I₀ e xf a j S Λ x₀ T T' T₀ h γ hγ1 z.2 hz2
    have hz : ∀ i, 0 < detNorm I.E (j i) (z.1 i) := by
      intro i
      refine (detNorm_pos_iff _).2 fun w => ?_
      have : Matrix.of (z.1 i w) = (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E).map w.embedding := by
        ext r s
        exact hγ2 i w r s
      rw [this]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((γ i).isUnit.map w.embedding.mapMatrix)).ne_zero
    have hP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
    have hact : ∀ (v) {p : Type} (X : Matrix (Fin I.n) p I.E),
        uMat (g v) * ((I.P v)⁻¹ * X.map (I.φ v)) = (I.P v)⁻¹ * (Γ * X).map (I.φ v) := by
      intro v p X
      rw [g1, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), hP, Matrix.one_mul, Matrix.map_mul, Matrix.mul_assoc]
    have hA : ∀ v i, uMat (g v) * ((I.P v)⁻¹ * (T i).map (I.φ v)) =
        (I.P v)⁻¹ * (T i).map (I.φ v) * (Matrix.of ((R z v).1 i)).map (τ v) := by
      intro v i
      rw [hact, g3, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext r s
      exact (hβ v _).trans (congrArg (τ v) (hγ2 i (β v) r s).symm)
    have hA₀ : ∀ v, uMat (g v) * ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v)) =
        (I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v) * (uMat (R z v).2).map (τ₀ v) := by
      intro v
      have e1 : (γ₀.map e).map (I.φ v) = (γ₀.map (I₀.φ (σ v))).map (τ₀ v) := by
        ext r s
        exact hσ v _
      have e2 : uMat (R z v).2 = _ := g2 (σ v)
      rw [← Matrix.mul_assoc, hact, g4, Matrix.map_mul, e1, e2, Matrix.map_mul, Matrix.map_mul,
        Matrix.mul_assoc _ ((I₀.P (σ v)).map (τ₀ v)), ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)),
        ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)), inv_map _ (I₀.P_unit _), Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    refine ⟨fun v => θ v (R z v), ⟨hM z hz, g, ⟨hg, fun v k y hy => ?_⟩, g * (fun v => θ v (R z v))⁻¹,
      fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).2 (g v) (hA v) (hA₀ v), (inv_mul_cancel_right _ _).symm⟩,
      funext fun v => ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).1⟩
    have hsp := GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis I I₀ e xf a j S Λ x₀ T T' T₀ h v
    obtain ⟨u, hu, rfl⟩ := (hsp k y).1 hy
    refine (hsp k _).2 ⟨fun i => (Matrix.of ((R z v).1 i)).map (τ v) *ᵥ u i, fun i hi => ?_, ?_⟩
    · simp only [hu i hi, Matrix.mulVec_zero]
    · simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, hA]
  · have h0 : ∀ v, uMat ((1 : I.Ginf) v) = 1 := fun v => rfl
    have h1 := GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move I xf a j hj S hsat 1 (fun v => θ v (R z v)) 1
      (fun v => ⟨fun i y _ => by rw [h0]; simp, fun y _ => by rw [h0]; simp⟩) (hM z hz)
      (fun v => show (uMat ((1 : I.Ginf) v))ᴴ * uMat ((1 : I.Ginf) v) = 1 by rw [h0]; simp) i
    rw [one_mul, mul_one] at h1
    refine size_solve hf (hj i) (hpos 1 i) (hpos _ i) (hz i) (h1.trans ?_)
    congr 1
    simp only [fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).1 i]
    have hj' : (j i : ℝ) ≠ 0 := by have := hj i; positivity
    rw [detNorm, ← Real.finset_prod_rpow _ _ (fun w _ => by positivity)]
    refine Fintype.prod_equiv β _ _ fun v => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    field_simp
  · have h1 : ∀ v, R z v = R z' v := fun v =>
      ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).2 (congrFun hzz v)
    refine Prod.ext (funext fun i => funext fun w => ?_) (funext fun w => ?_)
    · obtain ⟨v, rfl⟩ := β.surjective w
      exact congrFun (congrArg Prod.fst (h1 v)) i
    · obtain ⟨v, rfl⟩ := σ.surjective w
      exact congrArg Prod.snd (h1 v)
  · have hd : I.n - 2 * ∑ i, j i = I₀.n := by rw [h.2.1]; omega
    rw [hd] at hμ
    have h1 := funext fun v => (hθ v).2.2.2.2 (μM v) (c₀ (σ v)) (hμ v) (hc₀ (σ v))
    have h2 := measurePreserving_pi _ μM (f := θ) fun v => ⟨(hθ v).1, (congrFun h1 v).symm⟩
    have h3 := (h2.comp hR).lintegral_comp hφ
    have h4 : (Measure.pi fun i => haarGL I.E (j i)).restrict {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)} =
        Measure.pi fun i => haarGL I.E (j i) := Measure.restrict_eq_self_of_ae_mem (ae_detNorm_pos I.E j)
    rw [← h3, lintegral_smul_measure, h4, smul_eq_mul, hcard]
    simp only [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    congr 1
    · simp only [← pow_mul, mul_comm]
    · exact lintegral_prod _ (hφ.comp hΘ).aemeasurable

end GlobalTheory.LeviIso
