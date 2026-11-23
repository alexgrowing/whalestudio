import Development.WeilBound.ThetaLifts.LeviDeterminants.EvFrame

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

set_option maxHeartbeats 1600000 in
theorem adapted_plane_model_evaluation_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoB H H') e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  classical
  obtain ⟨Q, h⟩ := frOK_herm hB hH hX
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F Q * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F Q * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (incM F H.ι * z * (incM F H'.ι)ᵀ) = Matrix.fromBlocks z 0 0 0 := fun z => by
    rw [hw, w_mul, h.qi, h'.qi]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have hπ : ∀ v, ∀ γ ∈ latAtV X W v, (w γ).submatrix .inl .inl ∈ latAtV X₁ W₁ v := fun v γ hγ =>
    lat_map (X₁ := X₁) (W₁ := W₁) h.low h'.low hγ
  have qv : ∀ z, incM F Q *ᵥ (incM F H.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h.qi]; ext (i | i) <;> simp
  have qv' : ∀ z, incM F Q' *ᵥ (incM F H'.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h'.qi]; ext (i | i) <;> simp
  let G : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) E := (frame H')ᵀ * W.J * (frame H').map σ
  have hG : incM F G = Matrix.fromBlocks (incM F W₁.J) 0 0 !![0, 1; -1, 0] := by
    have := h'.gram
    rw [Int.cast_neg, Int.cast_one] at this
    rw [← this, incM_mul, incM_mul]
    rfl
  have hGh : ∀ i j, cA σ (incM F G j i) = -1 * incM F G i j := fun i j => by
    have := inc_herm (F := F) (η := -1) (J := G) (gram_herm σ (conj_conj hB) (fun i j => by simp [hW.skew]) _) i j
    rwa [Int.cast_neg, Int.cast_one] at this
  obtain ⟨A0, a0, e0⟩ := h.msk 0 1 0
  obtain ⟨A1, a1, e1⟩ := h.msk 1 0 0
  obtain ⟨C0, c0, f0⟩ := h'.msk 1 1 1
  obtain ⟨C1, c1, f1⟩ := h'.msk 0 1 0
  obtain ⟨Ma, e, h1, h2⟩ := exists_model hB hX hW hM hM₁ (κ := (Fin d₁ ⊕ Fin 2) ⊕ Fin n₁) (by simp [hH.rank, hH'.rank]; ring)
    (fun z => Sum.elim (w z (.inr 1)) (fun i => ((w z).submatrix .inl id) i (.inr 1)))
    (fun z => Sum.elim (DL (cA σ) (incM F G) (w z)) (DR (cA σ) (incM F X₁.J) ((w z).submatrix .inl id)))
    (fun z => (w z).submatrix .inl .inl)
    ⟨fun z z' => by ext (k | k) <;> simp, fun c z => by ext (k | k) <;> simp⟩
    ⟨fun z z' => by ext (k | k) <;> simp only [map_add, DR, DL, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.add_apply,
        Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib, neg_add],
      fun c z => by ext (k | k) <;> simp [DR, DL, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g := h.gram
      rw [Int.cast_one] at g
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one, ← hG] at g'
      rw [hTens_fr _ _ h.pq h'.pq, g, g', splitL _ hc _ hGh, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, map_add]
      conv_lhs => rw [hG, splitR _ hc (fun i j => by simpa using h.herm₁ i j), ← hG]
      simp only [← hw]
      rw [show ∀ z, ((w z).submatrix Sum.inl id).submatrix id Sum.inl = (w z).submatrix .inl .inl from fun _ => rfl,
        show ∀ z, ((w z).submatrix Sum.inl id).submatrix id Sum.inl = (w z).submatrix .inl .inl from fun _ => rfl]
      ring)
    (fun x => by
      simp only [hw, w_inc]
      generalize Q * x * Q'ᵀ = y
      refine ⟨⟨Sum.elim (y (.inr 1)) (fun i => (y.submatrix .inl id) i (.inr 1)), by ext (k | k) <;> rfl⟩,
        ⟨Sum.elim (DL σ G y) (DR σ X₁.J (y.submatrix .inl id)), ?_⟩, y.submatrix .inl .inl, rfl⟩
      ext (k | k)
      · exact congrFun (DL_inc G y) k
      · exact congrFun (DR_inc X₁.J (y.submatrix .inl id)) k)
    H.ι H'.ι (isoB H H') (fun z => by
      simp only [hi]
      exact ⟨by ext ((k | k) | k) <;> simp, by ext; simp⟩)
    (by
      rintro u (⟨y, rfl⟩ | ⟨y, rfl⟩)
      · simp only [hw, w_vec, h.qx]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩
      · simp only [hw, w_vec, h'.qx, qv]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨hπ v γ hγ, _, add_mem (lat_map a0 c0 hγ) (lat_map a1 c1 hγ), by
      simp only [map_add]
      simp only [hw, w_msk e0 f0, w_msk e1 f1]
      generalize incM F Q * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext ((k | k) | k) <;> simp [mask]
      · ext; simp [mask]
      · ext (k | k)
        · simp only [Sum.elim_inl, DL]
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 2
          rcases l with l | l
          · simp [mask]
          · fin_cases l <;> simp [mask]
        · simp [DR, mask]⟩)
  exact ⟨Ma, e, h1, h2⟩

end PositivityTheory.ThKF0
