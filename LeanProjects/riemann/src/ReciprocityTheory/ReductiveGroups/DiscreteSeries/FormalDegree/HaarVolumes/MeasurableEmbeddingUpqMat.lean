import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQ

noncomputable section

open Finset Matrix MeasureTheory Topology Filter

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ} {P Q : ℕ}

def gMatL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' s t := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp [star_add] <;> ring
  map_smul' c s := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul] <;> ring

theorem norm_le_sum_gMat {ε : Fin n → Bool} (s : GCo ε) : ‖s‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖ := by
  have hS : ∀ a b, ‖gMat s a b‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖ := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖gMat s a b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖gMat s a b‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
  have h0 : 0 ≤ ∑ a, ∑ b, ‖gMat s a b‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun a => (le_of_eq ?_).trans (hS a a)
    simp [gMat, kMat, pmat]
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)
    obtain ⟨⟨a, b⟩, h⟩ := ab
    have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => h'.2 h.2
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h' => lt_asymm h'.1 h.1
    have h3 : a ≠ b := h.1.ne'
    simp [gMat, kMat, pmat, h3, h, h1, h2]
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)
    obtain ⟨⟨a, b⟩, h⟩ := ab
    have h1 : ¬ (b < a ∧ ε a = ε b) := fun h' => h.2 h'.2
    have h2 : ¬ (a < b ∧ ε b = ε a) := fun h' => lt_asymm h'.1 h.1
    have h3 : a ≠ b := h.1.ne'
    simp [gMat, kMat, pmat, h3, h, h1, h2]

theorem gco_haar (ε : Fin n → Bool) :
    (volume : Measure (KCo ε)).IsAddHaarMeasure ∧ (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure ∧
      (volume : Measure (GCo ε)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℝ)).IsAddHaarMeasure; infer_instance
  have h2 : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance
  have h3 : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance
  have h4 : (volume : Measure (KCo ε)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (KPair ε → ℂ))).IsAddHaarMeasure
    infer_instance
  refine ⟨h4, h3, ?_⟩
  show ((volume : Measure (KCo ε)).prod (volume : Measure (PCoord ε → ℂ))).IsAddHaarMeasure
  exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

theorem upqT_borel (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

theorem lieU_borel (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

theorem Jpq_eq_diag (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.UG.Jpq P Q = Matrix.diagonal (fun i => if ε (e i) = true then (1 : ℂ) else -1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal_apply, he1, he2, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem Jm_eq_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Jm ε = Matrix.reindex e e (Formalism.UG.Jpq P Q) := by
  rw [Jpq_eq_diag e he1 he2]
  ext a b
  simp [Jm, Matrix.diagonal_apply]

def yE (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) : ℂ :=
  (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (e.symm a) (e.symm b)

theorem lie_rel (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) :
    star (yE e X b a) * (if ε b = true then (1 : ℂ) else -1) +
      (if ε a = true then (1 : ℂ) else -1) * yE e X a b = 0 := by
  have h : (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 := X.2
  rw [Jpq_eq_diag e he1 he2] at h
  have h' := congrFun (congrFun h (e.symm a)) (e.symm b)
  simpa [yE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

theorem lie_rel_c (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) (h : ε a = ε b) : yE e X a b = -star (yE e X b a) := by
  have R := lie_rel e he1 he2 X a b
  rw [← h] at R
  simp only [Complex.star_def] at R ⊢
  cases ha : ε a <;> simp [ha] at R <;> first | linear_combination R | linear_combination -R

theorem lie_rel_nc (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) (h : ε a ≠ ε b) : yE e X a b = star (yE e X b a) := by
  have R := lie_rel e he1 he2 X a b
  simp only [Complex.star_def] at R ⊢
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at R h ⊢ <;>
    first | linear_combination R | linear_combination -R

theorem lie_rel_d (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a : Fin n) : (yE e X a a).re = 0 := by
  have R := congrArg Complex.re (lie_rel e he1 he2 X a a)
  cases ha : ε a <;> simp [ha] at R <;> linarith

def sOfLie (e : Fin P ⊕ Fin Q ≃ Fin n) (ε : Fin n → Bool) (X : Formalism.BasicNotions.lieU P Q) : GCo ε :=
  (((fun a => (yE e X a a).im), fun ab => yE e X ab.1.1 ab.1.2), fun ab => yE e X ab.1.1 ab.1.2)

theorem gMat_sOfLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) : gMat (sOfLie e ε X) a b = yE e X a b := by
  simp only [gMat, kMat, pmat, sOfLie, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have n1 : a ≠ b := hab.ne
    have n2 : ¬ (b < a) := not_lt.2 hab.le
    by_cases hε : ε a = ε b
    · simp [n1, n2, hab, hε]
      exact (lie_rel_c e he1 he2 X a b hε).symm
    · have hε' : ε b ≠ ε a := Ne.symm hε
      simp [n1, n2, hab, hε, hε']
      exact (lie_rel_nc e he1 he2 X a b hε).symm
  · have hre := lie_rel_d e he1 he2 X a
    simp
    apply Complex.ext <;> simp [hre]
  · have n1 : a ≠ b := hab.ne'
    have n2 : ¬ (a < b) := not_lt.2 hab.le
    by_cases hε : ε a = ε b
    · simp [n1, n2, hab, hε]
    · simp [n1, n2, hab, hε]

theorem gToLie_surj (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) : gToLie e he1 he2 (sOfLie e ε X) = X := by
  apply Subtype.ext
  ext i j
  show Matrix.reindex e.symm e.symm (gMat (sOfLie e ε X)) i j = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [gMat_sOfLie e he1 he2 X]
  simp [yE]

theorem exp_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    Matrix.reindex e e (NormedSpace.exp X) = NormedSpace.exp (Matrix.reindex e e X) := by
  have hc : Continuous (fun M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Matrix.reindex e e M) :=
    continuous_id.matrix_submatrix _ _
  have hc' : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M) :=
    continuous_id.matrix_submatrix _ _
  simp only [NormedSpace.exp_eq_tsum_rat]
  show (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom (∑' k : ℕ, ((k.factorial : ℚ)⁻¹ : ℚ) • X ^ k) = _
  rw [Function.LeftInverse.map_tsum (g := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom) _ (by exact hc) (by exact hc')
    (fun M => by ext i j; simp)]
  simp only [map_rat_smul, map_pow]
  rfl

theorem cT_eq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : Formalism.UG.cT (starRingEnd ℂ) A = Aᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem Jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem reindex_form (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Matrix.reindex e e A)ᴴ * Jm ε * Matrix.reindex e e A = Matrix.reindex e e (Aᴴ * Formalism.UG.Jpq P Q * A) := by
  rw [Jm_eq_reindex e he1 he2]
  simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

def upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) (g : Formalism.BasicNotions.UpqT P Q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)

theorem mem_Upq_iff (g : GL (Fin P ⊕ Fin Q) ℂ) :
    g ∈ Formalism.UG.Upq P Q ↔
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q * g = Formalism.UG.Jpq P Q := by
  rw [← cT_eq]; exact Iff.rfl

theorem mat_mem (g : Formalism.BasicNotions.UpqT P Q) :
    (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g = Formalism.UG.Jpq P Q :=
  (mem_Upq_iff _).1 (show Formalism.UG.Upq P Q from g).2

theorem mat_inv (g : Formalism.BasicNotions.UpqT P Q) :
    ((((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) :
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      Formalism.UG.Jpq P Q * (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q := by
  apply Units.inv_eq_of_mul_eq_one_left
  have h := mat_mem g
  calc Formalism.UG.Jpq P Q * (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g
      = Formalism.UG.Jpq P Q * ((Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jpq_mul_self]

theorem upqMat_inUJ (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (g : Formalism.BasicNotions.UpqT P Q) : inUJ ε (upqMat e g) := by
  unfold inUJ upqMat
  rw [reindex_form e he1 he2, mat_mem, ← Jm_eq_reindex e he1 he2]

theorem range_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Set.range (upqMat e) = {M | inUJ ε M} := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact upqMat_inUJ e he1 he2 g
  · intro hM
    set A := Matrix.reindex e.symm e.symm M with hA
    have hAM : Matrix.reindex e e A = M := by rw [hA]; ext a b; simp
    have hform : Aᴴ * Formalism.UG.Jpq P Q * A = Formalism.UG.Jpq P Q := by
      apply (Matrix.reindex e e).injective
      rw [← reindex_form e he1 he2, hAM, ← Jm_eq_reindex e he1 he2]
      exact hM
    have h2 : (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
      calc (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = Formalism.UG.Jpq P Q * (Aᴴ * Formalism.UG.Jpq P Q * A) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hform, Jpq_mul_self]
    have h1 : A * (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) = 1 := mul_eq_one_comm.mp h2
    let u : GL (Fin P ⊕ Fin Q) ℂ := ⟨A, Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q, h1, h2⟩
    have hu : u ∈ Formalism.UG.Upq P Q := (mem_Upq_iff u).2 hform
    refine ⟨(⟨u, hu⟩ : Formalism.UG.Upq P Q), ?_⟩
    exact hAM

theorem upqMat_cont (e : Fin P ⊕ Fin Q ≃ Fin n) : Continuous (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
  have h : Continuous fun g : Formalism.BasicNotions.UpqT P Q => Formalism.BasicNotions.UpqT.mat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_submatrix _ _

theorem isClosedEmbedding_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    IsClosedEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
  let f : Matrix (Fin n) (Fin n) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun M => (Matrix.reindex e.symm e.symm M,
      MulOpposite.op (Formalism.UG.Jpq P Q * (Matrix.reindex e.symm e.symm M)ᴴ * Formalism.UG.Jpq P Q))
  have hr : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M :=
    continuous_id.matrix_submatrix _ _
  have hf : Continuous f :=
    hr.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul hr.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ (upqMat e : Formalism.BasicNotions.UpqT P Q → _) =
      Units.embedProduct _ ∘ (fun g : Formalism.BasicNotions.UpqT P Q => ((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ)) := by
    funext g
    simp only [Function.comp_apply, f, Units.embedProduct_apply, upqMat]
    rw [mat_inv]
    simp
    rfl
  have hI : IsInducing (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
    refine IsInducing.of_comp (upqMat_cont e) hf ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal
  have hE : IsEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
    refine ⟨hI, fun a b h => ?_⟩
    have h' : Formalism.BasicNotions.UpqT.mat a = Formalism.BasicNotions.UpqT.mat b := (Matrix.reindex e e).injective h
    exact Subtype.ext (Units.ext h')
  refine ⟨hE, ?_⟩
  rw [range_upqMat e he1 he2]
  exact isClosed_inUJ ε

theorem measurableEmbedding_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    @MeasurableEmbedding (Formalism.BasicNotions.UpqT P Q) (Fin n → Fin n → ℂ) _ _ (fun g => upqMat e g) := by
  haveI := upqT_borel P Q
  exact Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ)
    (isClosedEmbedding_upqMat e he1 he2)

theorem measurableEmbedding_toM (ε : Fin n → Bool) :
    @MeasurableEmbedding (UJ ε) (Fin n → Fin n → ℂ) _ _ (fun g : UJ ε => toM g) :=
  Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) (isClosedEmbedding_toM ε)

theorem gToLie_val (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Matrix.reindex e e ((gToLie e he1 he2 s : Formalism.BasicNotions.lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      gMat s := by
  show Matrix.reindex e e (Matrix.reindex e.symm e.symm (gMat s)) = gMat s
  ext a b; simp

theorem image_expBall (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (r : ℝ) :
    upqMat e '' {g : Formalism.BasicNotions.UpqT P Q | ∃ X ∈ Formalism.BasicNotions.ballU P Q r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} =
      (fun g : UJ ε => toM g) '' expSet {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} := by
  ext M
  constructor
  · rintro ⟨g, ⟨X, hX, hgX⟩, rfl⟩
    have hin : upqMat e g ∈ Set.range (fun u : UJ ε => toM u) := by
      rw [range_toM]; exact upqMat_inUJ e he1 he2 g
    obtain ⟨u, hu⟩ := hin
    refine ⟨u, ⟨sOfLie e ε X, ?_, ?_⟩, hu⟩
    · show gToLie e he1 he2 (sOfLie e ε X) ∈ Formalism.BasicNotions.ballU P Q r
      rw [gToLie_surj]; exact hX
    · have hu' : toM u = upqMat e g := hu
      rw [hu', upqMat, hgX, exp_reindex, ← gToLie_val e he1 he2, gToLie_surj]
  · rintro ⟨u, ⟨s, hs, hus⟩, rfl⟩
    have hin : toM u ∈ Set.range (upqMat e) := by
      rw [range_upqMat e he1 he2]; exact u.2
    obtain ⟨g, hg⟩ := hin
    refine ⟨g, ⟨gToLie e he1 he2 s, hs, ?_⟩, hg⟩
    apply (Matrix.reindex e e).injective
    rw [exp_reindex, gToLie_val e he1 he2]
    show upqMat e g = _
    rw [hg, hus]

end ReciprocityTheory.ChartRestriction.DS
