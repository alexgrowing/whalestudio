import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityMuCDtr

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

namespace UpperTriangularPsiTransport

local instance instTGUpqT (P Q : ℕ) : IsTopologicalGroup (Formalism.BasicNotions.UpqT P Q) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))

local instance instBorelUpqT (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

def reU {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) : GL (Fin P ⊕ Fin Q) ℂ ≃* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv

lemma Jpq_eq {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.UG.Jpq P Q = (Jm ε).submatrix e e := by
  ext i j
  simp only [Matrix.submatrix_apply, Jm, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, he1, he2, Matrix.one_apply]
  all_goals
    try split_ifs
    all_goals simp_all

lemma cT_eq {m : Type} (M : Matrix m m ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  rfl

lemma map_eq {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    (Formalism.UG.Upq P Q).map ((reU e : GL (Fin P ⊕ Fin Q) ℂ ≃* (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      GL (Fin P ⊕ Fin Q) ℂ →* (Matrix (Fin n) (Fin n) ℂ)ˣ) = UJ ε := by
  have hJ := Jpq_eq e he1 he2
  have hJ' : Jm ε = (Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
    rw [hJ, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  have hval : ∀ h : GL (Fin P ⊕ Fin Q) ℂ,
      ((reU e h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.reindex e e (h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := fun h => rfl
  have hk : ∀ M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ,
      (Matrix.reindex e e M)ᴴ * Jm ε * Matrix.reindex e e M =
        Matrix.reindex e e (Mᴴ * Formalism.UG.Jpq P Q * M) := by
    intro M
    simp only [Matrix.reindex_apply]
    rw [hJ', Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : (h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q := by
      rw [← cT_eq]
      exact hh
    show (Matrix.reindex e e (h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))ᴴ * Jm ε *
        Matrix.reindex e e (h : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Jm ε
    rw [hk, hh', Matrix.reindex_apply, ← hJ']
  · intro hg
    have hg' : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g = Jm ε := hg
    refine ⟨(reU e).symm g, ?_, by simp⟩
    have hgM : (g : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.reindex e e (((reU e).symm g : GL (Fin P ⊕ Fin Q) ℂ) :
          Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
      rw [← hval, MulEquiv.apply_symm_apply]
    show Formalism.UG.cT (starRingEnd ℂ) (((reU e).symm g : GL (Fin P ⊕ Fin Q) ℂ) :
        Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) * Formalism.UG.Jpq P Q *
        (((reU e).symm g : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
          Formalism.UG.Jpq P Q
    rw [cT_eq]
    apply (Matrix.reindex e e).injective
    rw [← hk, ← hgM, hg', Matrix.reindex_apply, ← hJ']

def psi {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.UpqT P Q ≃* UJ ε :=
  ((reU e).subgroupMap (Formalism.UG.Upq P Q)).trans (MulEquiv.subgroupCongr (map_eq e he1 he2))

lemma psi_cont {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Continuous (psi e he1 he2) := by
  have hre : Continuous (fun M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Matrix.reindex e e M) := by
    exact continuous_id.matrix_reindex e e
  have hc : Continuous (fun g : ↥(Formalism.UG.Upq P Q) => (g : GL (Fin P ⊕ Fin Q) ℂ)) :=
    continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · exact hre.comp (Units.continuous_val.comp hc)
  · exact hre.comp (Units.continuous_coe_inv.comp hc)

lemma psi_symm_cont {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Continuous (psi e he1 he2).symm := by
  have hre : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.submatrix e e) := by
    exact continuous_id.matrix_submatrix e e
  have hc : Continuous (fun g : ↥(UJ ε) => (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
    continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · exact hre.comp (Units.continuous_val.comp hc)
  · exact hre.comp (Units.continuous_coe_inv.comp hc)

def psiC {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.UpqT P Q ≃ₜ* UJ ε :=
  { psi e he1 he2 with
    continuous_toFun := psi_cont e he1 he2
    continuous_invFun := psi_symm_cont e he1 he2 }

def psiM {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.UpqT P Q ≃ᵐ UJ ε :=
  (psiC e he1 he2).toHomeomorph.toMeasurableEquiv

private theorem jm_sq_lemma (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

private theorem isClosedEmbedding_coe_of_mem_iff_conjTranspose_Jm_mul_eq (ε : Fin n → Bool) (H : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hH : ∀ g : (Matrix (Fin n) (Fin n) ℂ)ˣ, g ∈ H ↔
      (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) :
    Topology.IsClosedEmbedding
      (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
  set J := Formalism.REAL.Jm ε with hJdef
  have hJJ : J * J = 1 := jm_sq_lemma ε
  have hleft : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * J * M = J → (J * Mᴴ * J) * M = 1 := by
    intro M hM
    calc J * Mᴴ * J * M = J * (Mᴴ * J * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, hJJ]
  have hinv : ∀ g : H, (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ) = J * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * J := by
    intro g
    exact Units.inv_eq_of_mul_eq_one_left (hleft _ ((hH _).1 g.2))
  have hcont : Continuous (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hct : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => J * Mᴴ * J) := by
    exact (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hψ : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (J * Mᴴ * J))) := by
    exact continuous_id.prodMk (MulOpposite.continuous_op.comp hct)
  have hcomp : ((fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (J * Mᴴ * J))) ∘
      (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))) =
      (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘ (Subtype.val : H → (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    funext g
    simp only [Function.comp_apply, Units.embedProduct_apply, hinv]
  have hind : Topology.IsInducing ((fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (J * Mᴴ * J))) ∘
      (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))) := by
    rw [hcomp]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hemb : Topology.IsEmbedding
      (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) :=
    ⟨Topology.IsInducing.of_comp hcont hψ hind, fun a b hab => Subtype.ext (Units.ext hab)⟩
  refine ⟨hemb, ?_⟩
  have hrange : Set.range (fun g : H => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
      {M | Mᴴ * J * M = J} := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact (hH _).1 g.2
    · intro hM
      have h1 := hleft M hM
      have h2 : M * (J * Mᴴ * J) = 1 := mul_eq_one_comm.1 h1
      exact ⟨⟨⟨M, J * Mᴴ * J, h2, h1⟩, (hH _).2 hM⟩, rfl⟩
  rw [hrange]
  have hq : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Mᴴ * J * M) := by
    exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hq continuous_const

lemma toM_emb (ε : Fin n → Bool) :
    MeasurableEmbedding (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := by
  have h := isClosedEmbedding_coe_of_mem_iff_conjTranspose_Jm_mul_eq ε (UJ ε) (fun g => Iff.rfl)
  exact Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) h

lemma umat_emb (ε : Fin n → Bool) :
    MeasurableEmbedding (β := Fin n → Fin n → ℂ) (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
  have h := isClosedEmbedding_coe_of_mem_iff_conjTranspose_Jm_mul_eq ε (Formalism.REAL.UJ ε) (fun g => Iff.rfl)
  exact Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) h

lemma key (cd : Formalism.BasicNotions.CDHaar) {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    ∃ a : ENNReal, a ≠ ⊤ ∧ ∀ E : Set (Formalism.BasicNotions.UpqT P Q),
      cd.cd P Q E * ENNReal.ofReal (cPQ ε) = a * muCDtr e ε E := by
  have := cd.haar P Q
  have := muPolar_isHaar ε
  have : (Measure.map (psiC e he1 he2) (cd.cd P Q)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map (cd.cd P Q) (psiC e he1 he2)
  have hmap : Measure.map (psiM e he1 he2) (cd.cd P Q) = Measure.map (psiC e he1 he2) (cd.cd P Q) := rfl
  obtain ⟨s, hs⟩ : ∃ s : NNReal, Measure.map (psiC e he1 he2) (cd.cd P Q) = s • muPolar ε :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.map (psiC e he1 he2) (cd.cd P Q)) (muPolar ε)⟩
  refine ⟨(s : ENNReal), ENNReal.coe_ne_top, fun E => ?_⟩
  have hemb : MeasurableEmbedding (β := Fin n → Fin n → ℂ)
      (fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) :=
    (toM_emb ε).comp (psiM e he1 he2).measurableEmbedding
  have h1 : cd.cd P Q E = Measure.map (psiM e he1 he2) (cd.cd P Q) (psiM e he1 he2 '' E) := by
    rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ (psiM e he1 he2).injective]
  have h2 : muPolar ε (psiM e he1 he2 '' E) =
      muPolarMat ε ((fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) '' E) := by
    unfold muPolar
    rw [(toM_emb ε).comap_apply]
    exact congrArg (muPolarMat ε) (Set.image_image _ _ _)
  have h3 : muCDtr e ε E = ENNReal.ofReal (cPQ ε) *
      muPolarMat ε ((fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) '' E) := by
    unfold muCDtr
    rw [hemb.comap_apply, Measure.smul_apply, smul_eq_mul]
  rw [h1, hmap, hs, Measure.coe_nnreal_smul_apply, h2, h3]
  ring

lemma isOmegaLeb_unique {P Q : ℕ} (lam lam' : Measure (Formalism.BasicNotions.lieU P Q)) (h : Formalism.BasicNotions.IsOmegaLeb lam)
    (h' : Formalism.BasicNotions.IsOmegaLeb lam') : lam = lam' := by
  obtain ⟨hH, hv⟩ := h
  obtain ⟨hH', hv'⟩ := h'
  haveI := hH
  haveI := hH'
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have hcl : IsClosed (Formalism.BasicNotions.lieU P Q : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) := by
    have hset : (Formalism.BasicNotions.lieU P Q : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
        {X | Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0} := rfl
    rw [hset]
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)) continuous_const
  haveI : LocallyCompactSpace ↥(Formalism.BasicNotions.lieU P Q) := hcl.locallyCompactSpace
  haveI : SecondCountableTopology ↥(Formalism.BasicNotions.lieU P Q) :=
    inferInstanceAs (SecondCountableTopology ↥(Formalism.BasicNotions.lieU P Q : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, lam = c • lam' := by
    exact ⟨_, MeasureTheory.Measure.isAddLeftInvariant_eq_smul_of_innerRegular lam lam'⟩
  have hvol : (c * c) • (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) = volume := by
    conv_rhs => rw [← hv]
    rw [hsm, MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right,
      MeasureTheory.Measure.map_smul, MeasureTheory.Measure.map_smul, hv', smul_smul]
  have hpos : 0 < (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ))
      (Metric.ball 0 1) := Metric.measure_ball_pos _ _ one_pos
  have hfin : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hcc : c * c = 1 := by
    have h1 := congrArg (fun μ : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) =>
      μ (Metric.ball 0 1)) hvol
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    generalize hvdef : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ))
      (Metric.ball 0 1) = v at h1 hpos hfin
    calc c * c = c * c * (v * v⁻¹) := by rw [ENNReal.mul_inv_cancel hpos.ne' hfin, mul_one]
      _ = c * c * v * v⁻¹ := (mul_assoc (c * c) v v⁻¹).symm
      _ = v * v⁻¹ := by rw [h1]
      _ = 1 := ENNReal.mul_inv_cancel hpos.ne' hfin
  have hc1 : c = 1 := by
    rcases lt_trichotomy c 1 with h1 | h1 | h1
    · exfalso
      have h2 : c * c < 1 := by
        calc c * c ≤ c * 1 := by
              have h3 := h1.le
              gcongr
          _ = c := mul_one c
          _ < 1 := h1
      exact h2.ne hcc
    · exact h1
    · exfalso
      have h2 : 1 < c * c := by
        calc (1 : ENNReal) < c := h1
          _ = c * 1 := (mul_one c).symm
          _ ≤ c * c := by
              have h3 := h1.le
              gcongr
      exact h2.ne' hcc
  rw [hsm, hc1, one_smul]

lemma omegaDensity_unique {P Q : ℕ} {μ : Measure (Formalism.BasicNotions.UpqT P Q)} {c c' : ENNReal}
    (h : Formalism.BasicNotions.OmegaDensity μ c) (h' : Formalism.BasicNotions.OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, hlam, hc⟩ := h
  obtain ⟨lam', hlam', hc'⟩ := h'
  obtain rfl : lam' = lam := isOmegaLeb_unique lam' lam hlam' hlam
  exact tendsto_nhds_unique hc hc'

lemma omegaDensity_rel {P Q : ℕ} {μ ν : Measure (Formalism.BasicNotions.UpqT P Q)} {a b c d : ENNReal}
    (hb : b ≠ ⊤) (hd : d ≠ 0) (hrel : ∀ E, μ E * b = a * ν E)
    (hμ : Formalism.BasicNotions.OmegaDensity μ c) (hν : Formalism.BasicNotions.OmegaDensity ν d) : c * b = a * d := by
  obtain ⟨lam, hlam, hc⟩ := hμ
  obtain ⟨lam', hlam', hd'⟩ := hν
  obtain rfl : lam' = lam := isOmegaLeb_unique lam' lam hlam' hlam
  have h1 := ENNReal.Tendsto.mul_const hc (Or.inr hb)
  have h2 := ENNReal.Tendsto.const_mul (a := a) hd' (Or.inl hd)
  refine tendsto_nhds_unique h1 (h2.congr fun r => ?_)
  simp only [div_eq_mul_inv]
  rw [← mul_assoc, ← hrel, mul_right_comm]

end UpperTriangularPsiTransport

open UpperTriangularPsiTransport in
theorem muCD_eq_cd_vol (cd : Formalism.BasicNotions.CDHaar) {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Set (Formalism.REAL.UJ ε)) (hA : MeasurableSet A) :
    muCD ε A = cd.cd P Q {g | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)} := by
  obtain ⟨a, -, hrel⟩ := key cd e he1 he2
  have hn : P + Q = n := by simpa using Fintype.card_congr e
  obtain ⟨c', -, -, h1, h2⟩ := cd.trick P Q
  have hc' : c' = ENNReal.ofReal (cOmega (P + Q)) := omegaDensity_unique h2 (omegaDensity_cd cd (P + Q))
  have hc0 : ENNReal.ofReal (cPQ ε) ≠ 0 := by simpa using cPQ_pos ε
  have hw0 : ENNReal.ofReal (cOmega n) ≠ 0 := by simpa using cOmega_pos n
  have hrel2 := omegaDensity_rel ENNReal.ofReal_ne_top hw0 hrel h1 (omegaDensity_muCDtr e he1 he2)
  rw [hc', hn, mul_comm a] at hrel2
  have hac : a = ENNReal.ofReal (cPQ ε) :=
    ((ENNReal.mul_right_inj hw0 ENNReal.ofReal_ne_top).1 hrel2).symm
  set E := {g : Formalism.BasicNotions.UpqT P Q | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}
    with hEdef
  have hE := hrel E
  rw [hac, mul_comm] at hE
  rw [(ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top).1 hE]
  have hemb : MeasurableEmbedding (β := Fin n → Fin n → ℂ)
      (fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) :=
    (toM_emb ε).comp (psiM e he1 he2).measurableEmbedding
  have himg : (fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) '' E =
      (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) '' A := by
    ext M
    constructor
    · rintro ⟨g, ⟨x, hx, hxg⟩, rfl⟩
      exact ⟨x, hx, hxg⟩
    · rintro ⟨x, hx, rfl⟩
      have hx2 : x.1 ∈ UJ ε := by rw [← real_UJ_eq_UJ ε]; exact x.2
      have hy := congrArg (fun y : UJ ε => toM y) ((psi e he1 he2).apply_symm_apply ⟨x.1, hx2⟩)
      exact ⟨(psi e he1 he2).symm ⟨x.1, hx2⟩, ⟨x, hx, hy.symm⟩, hy⟩
  have hL : muCD ε A = ENNReal.ofReal (cPQ ε) *
      muPolarMat ε ((fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) '' A) :=
    (Measure.smul_apply _ _ _).trans (congrArg _ ((umat_emb ε).comap_apply _ _))
  have hR : muCDtr e ε E = ENNReal.ofReal (cPQ ε) *
      muPolarMat ε ((fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) '' E) :=
    (hemb.comap_apply _ _).trans (Measure.smul_apply _ _ _)
  rw [hL, hR]
  exact congrArg (fun S => ENNReal.ofReal (cPQ ε) * muPolarMat ε S) himg.symm

end ReciprocityTheory.ChartRestriction.DS
