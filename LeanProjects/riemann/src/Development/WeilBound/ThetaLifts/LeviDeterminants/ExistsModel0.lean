import Development.WeilBound.ThetaLifts.LeviDeterminants.EvFrame

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

set_option maxHeartbeats 400000 in
theorem exists_model0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ →
    ∃ (κ₀ : Type) (_ : Fintype κ₀) (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n × Fin d₁) (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d₁)
      (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ 1 H'.ι (iso0 n H') e ∧
      (∀ z, Ma.co.e (z * (incM F H'.ι)ᵀ) = (glue ε 0 (M₁.co.e z).1, glue ε 0 (M₁.co.e z).2)) ∧
      (∀ y, ∃ q, Ma.co.e (Matrix.vecMulVec y (incV F H'.x)) = (0, glue ε q 0)) ∧
      (∀ y, ∃ p, Ma.co.e (Matrix.vecMulVec y (incV F H'.y)) = (glue ε p 0, 0)) ∧ (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH' hM₁
  classical
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (z * (incM F H'.ι)ᵀ) = Matrix.fromCols z 0 := fun z => by
    rw [hw, incM_one', Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h'.qi]
    ext i (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have h1 : ∀ u ∈ X.L, (1 : Matrix (Fin n) (Fin n) E) *ᵥ u ∈ X.L := fun u hu => by rwa [Matrix.one_mulVec]
  obtain ⟨C0, c0, f0⟩ := h'.msk 0 1 0
  obtain ⟨ε, Ma, e, p, q, hMa, hco, hp, hq, he, T, hT, hev⟩ := exists_modelS hB hX hW hM hM₁ (κ := Fin n)
    (by simp [hH'.rank]; ring) (fun z i => w z i (.inr 1)) (fun z => DR (cA σ) (incM F X.J) (w z))
    (fun z => (w z).submatrix id .inl) ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    ⟨fun z z' => by ext; simp only [map_add, DR, Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib, neg_add], fun c z => by ext; simp [DR, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one] at g'
      rw [hTens_fr _ _ (Matrix.one_mul 1) h'.pq, g', Matrix.transpose_one, Matrix.one_mul (incM F X.J),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        splitR _ hc (fun i j => by simpa using inc_herm (F := F) (η := 1) (J := X.J) (fun i j => by simp [hX.herm]) i j)]
      simp only [hw, incM_one'])
    (fun x => by
      simp only [hw, w_inc]
      generalize (1 : Matrix (Fin n) (Fin n) E) * x * Q'ᵀ = y
      exact ⟨⟨fun i => y i (.inr 1), rfl⟩, ⟨_, DR_inc X.J y⟩, y.submatrix id .inl, rfl⟩)
    1 H'.ι (iso0 n H') (fun z => by
      simp only [incM_one', Matrix.one_mul, hi]
      exact ⟨by ext; simp, by ext; simp⟩)
    (by
      rintro u ⟨y, rfl⟩
      simp only [hw, w_vec, h'.qx]
      exact ⟨by ext; simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨lat_map (X₁ := X) (W₁ := W₁) h1 h'.low hγ, _, lat_map h1 c0 hγ, by
      simp only [hw, w_msk (m := 1) (show incM F (1 : Matrix (Fin n) (Fin n) E) * incM F 1 = 1 * incM F 1 by
        rw [incM_one', Matrix.one_mul]) f0]
      generalize incM F (1 : Matrix (Fin n) (Fin n) E) * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext; simp [mask]
      · ext; simp [mask]
      · ext; simp [DR, mask]⟩)
  refine ⟨_, inferInstance, ε, Ma, e, T, hMa, he, fun z => ?_, fun y => ⟨q (Matrix.vecMulVec y (incV F H'.x)), ?_⟩,
    fun y => ⟨p (Matrix.vecMulVec y (incV F H'.y)), ?_⟩, hT, hev⟩
  · rw [hco, hp _ (by ext; simp [hi]), hq _ (by ext; simp [hi, DR]),
      show (w (z * (incM F H'.ι)ᵀ)).submatrix id Sum.inl = z by ext; simp [hi]]
  · have e1 : w (Matrix.vecMulVec y (incV F H'.x)) = Matrix.vecMulVec y (Pi.single (.inr 0) 1) := by
      rw [hw, w_vec, h'.qx, incM_one', Matrix.one_mulVec]
    rw [hco, hp _ (by ext; simp [e1, Matrix.vecMulVec_apply]),
      show (w (Matrix.vecMulVec y (incV F H'.x))).submatrix id Sum.inl = 0 by ext; simp [e1, Matrix.vecMulVec_apply], map_zero]
    exact Prod.ext (glue_zero ε) rfl
  · have e1 : w (Matrix.vecMulVec y (incV F H'.y)) = Matrix.vecMulVec y (Pi.single (.inr 1) 1) := by
      rw [hw, w_vec, h'.qy, incM_one', Matrix.one_mulVec]
    rw [hco, hq _ (by ext; simp [e1, DR, Matrix.vecMulVec_apply]),
      show (w (Matrix.vecMulVec y (incV F H'.y))).submatrix id Sum.inl = 0 by ext; simp [e1, Matrix.vecMulVec_apply], map_zero]
    exact Prod.ext rfl (glue_zero ε)

end PositivityTheory.ThKF0
