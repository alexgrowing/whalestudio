import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KDensA

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def kdPr (ε : Fin n → Bool) (s : Bool) (ij : {ab : Fin (kdC ε s) × Fin (kdC ε s) // ab.2 < ab.1}) :
    KPair ε :=
  ⟨(kdE ε s ij.1.1, kdE ε s ij.1.2), (kdE ε s).lt_iff_lt.2 ij.2, by rw [ε_kdE ε s, ε_kdE ε s]⟩

def kdCoS (ε : Fin n → Bool) (w : KCo ε) (s : Bool) : UCo (kdC ε s) :=
  (fun i => w.1 (kdE ε s i), fun ij => w.2 (kdPr ε s ij))

lemma kMat_eq_kdD {ε : Fin n → Bool} (w : KCo ε) : kMat w = kdD ε (fun s => skMat (kdCoS ε w s)) := by
  ext a b
  obtain ⟨⟨s, i⟩, rfl⟩ := (kdSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (kdSig ε).surjective b
  rw [kdD_apply]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.blockDiagonal'_apply_eq, kdSig_apply, kdSig_apply]
    have hE : ε (kdE ε s i) = ε (kdE ε s j) := by rw [ε_kdE ε s i, ε_kdE ε s j]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have h1 : kdE ε s i ≠ kdE ε s j := (kdE ε s).injective.ne hij.ne
      have h2 : ¬ (kdE ε s j < kdE ε s i ∧ ε (kdE ε s i) = ε (kdE ε s j)) :=
        fun h => absurd ((kdE ε s).lt_iff_lt.1 h.1) (not_lt.2 hij.le)
      have h3 : kdE ε s i < kdE ε s j ∧ ε (kdE ε s j) = ε (kdE ε s i) :=
        ⟨(kdE ε s).lt_iff_lt.2 hij, hE.symm⟩
      simp only [kMat, skMat, kdCoS, if_neg h1, dif_neg h2, dif_pos h3, if_neg hij.ne,
        dif_neg (not_lt.2 hij.le), dif_pos hij]
      rfl
    · simp [kMat, skMat, kdCoS]
    · have h1 : kdE ε s i ≠ kdE ε s j := (kdE ε s).injective.ne hij.ne'
      have h2 : kdE ε s j < kdE ε s i ∧ ε (kdE ε s i) = ε (kdE ε s j) :=
        ⟨(kdE ε s).lt_iff_lt.2 hij, hE⟩
      simp only [kMat, skMat, kdCoS, if_neg h1, dif_pos h2, if_neg hij.ne', dif_pos hij]
      rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hst, kdSig_apply, kdSig_apply]
    have h1 := ε_kdE ε s i
    have h2 := ε_kdE ε t j
    have hne : kdE ε s i ≠ kdE ε t j := fun h => hst (by rw [← h1, ← h2, h])
    have hc2 : ¬ (kdE ε t j < kdE ε s i ∧ ε (kdE ε s i) = ε (kdE ε t j)) := fun h => hst (by
      have := h.2
      rw [h1, h2] at this
      exact this)
    have hc3 : ¬ (kdE ε s i < kdE ε t j ∧ ε (kdE ε t j) = ε (kdE ε s i)) := fun h => hst (by
      have := h.2
      rw [h1, h2] at this
      exact this.symm)
    simp only [kMat, if_neg hne, dif_neg hc2, dif_neg hc3]

lemma norm_kdCoS_le {ε : Fin n → Bool} (w : KCo ε) (s : Bool) : ‖kdCoS ε w s‖ ≤ ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le_max ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact norm_le_pi_norm w.1 (kdE ε s i)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ij => ?_
    exact norm_le_pi_norm w.2 (kdPr ε s ij)

lemma kdE_surj' (ε : Fin n → Bool) (s : Bool) (a : Fin n) (h : ε a = s) : ∃ i, kdE ε s i = a := by
  subst h
  exact kdE_surj ε a

def kdIx (ε : Fin n → Bool) : Fin (pOf ε) ⊕ Fin (qOf ε) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (kdE ε true) (kdE ε false)) (by
    constructor
    · rintro (i | i) (j | j) h
      · exact congrArg Sum.inl ((kdE ε true).injective h)
      · have h1 := ε_kdE ε true i
        have h2 := ε_kdE ε false j
        have h' : kdE ε true i = kdE ε false j := h
        rw [h', h2] at h1; exact absurd h1 (by decide)
      · have h1 := ε_kdE ε false i
        have h2 := ε_kdE ε true j
        have h' : kdE ε false i = kdE ε true j := h
        rw [h', h2] at h1; exact absurd h1 (by decide)
      · exact congrArg Sum.inr ((kdE ε false).injective h)
    · intro a
      cases h : ε a
      · obtain ⟨i, hi⟩ := kdE_surj' ε false a h
        exact ⟨Sum.inr i, hi⟩
      · obtain ⟨i, hi⟩ := kdE_surj' ε true a h
        exact ⟨Sum.inl i, hi⟩)

lemma kdPr_inj (ε : Fin n → Bool) (s : Bool) : Function.Injective (kdPr ε s) := by
  intro x y h
  have h1 : kdE ε s x.1.1 = kdE ε s y.1.1 := congrArg (fun z : KPair ε => z.1.1) h
  have h2 : kdE ε s x.1.2 = kdE ε s y.1.2 := congrArg (fun z : KPair ε => z.1.2) h
  exact Subtype.ext (Prod.ext ((kdE ε s).injective h1) ((kdE ε s).injective h2))

lemma kdPr_surj (ε : Fin n → Bool) (x : KPair ε) : ∃ ij, kdPr ε (ε x.1.1) ij = x := by
  obtain ⟨⟨a, b⟩, hba, hab⟩ := x
  obtain ⟨i, hi⟩ := kdE_surj ε a
  obtain ⟨j, hj⟩ := kdE_surj' ε (ε a) b hab.symm
  have hba' : b < a := hba
  refine ⟨⟨(i, j), (kdE ε (ε a)).lt_iff_lt.1 (by rw [hi, hj]; exact hba')⟩, ?_⟩
  apply Subtype.ext
  show (kdE ε (ε a) i, kdE ε (ε a) j) = (a, b)
  rw [hi, hj]

def kdPx (ε : Fin n → Bool) :
    {ab : Fin (pOf ε) × Fin (pOf ε) // ab.2 < ab.1} ⊕ {ab : Fin (qOf ε) × Fin (qOf ε) // ab.2 < ab.1} ≃
      KPair ε :=
  Equiv.ofBijective (Sum.elim (kdPr ε true) (kdPr ε false)) (by
    constructor
    · rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (kdPr_inj ε true h)
      · have h1 := ε_kdE ε true i.1.1
        have h2 := ε_kdE ε false j.1.1
        have h' : kdE ε true i.1.1 = kdE ε false j.1.1 := congrArg (fun z : KPair ε => z.1.1) h
        rw [h', h2] at h1; exact absurd h1 (by decide)
      · have h1 := ε_kdE ε false i.1.1
        have h2 := ε_kdE ε true j.1.1
        have h' : kdE ε false i.1.1 = kdE ε true j.1.1 := congrArg (fun z : KPair ε => z.1.1) h
        rw [h', h2] at h1; exact absurd h1 (by decide)
      · exact congrArg Sum.inr (kdPr_inj ε false h)
    · intro x
      obtain ⟨ij, hij⟩ := kdPr_surj ε x
      revert ij
      cases ε x.1.1
      · intro ij hij; exact ⟨Sum.inr ij, hij⟩
      · intro ij hij; exact ⟨Sum.inl ij, hij⟩)

def kdRe (α β γ δ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : ((α × β) × (γ × δ)) ≃ᵐ ((α × γ) × (β × δ)) :=
  (MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
    ((MeasurableEquiv.prodAssoc.symm.trans
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl δ))).trans
        MeasurableEquiv.prodAssoc))).trans MeasurableEquiv.prodAssoc.symm

private lemma measurePreserving_prodAssoc_volume {X Y Z : Type*} [MeasureSpace X] [MeasureSpace Y] [MeasureSpace Z]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)]
    [SigmaFinite (volume : Measure Z)] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (X × Y) × Z ≃ᵐ X × Y × Z) volume volume :=
  measurePreserving_prodAssoc volume volume volume

private lemma measurePreserving_prodComm_volume {X Y : Type*} [MeasureSpace X] [MeasureSpace Y]
    [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)] :
    MeasurePreserving (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X) volume volume :=
  Measure.measurePreserving_swap

lemma kdRe_mp {α β γ δ : Type*} [MeasureSpace α] [MeasureSpace β] [MeasureSpace γ] [MeasureSpace δ]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)] [SigmaFinite (volume : Measure γ)]
    [SigmaFinite (volume : Measure δ)] : MeasurePreserving (kdRe α β γ δ) volume volume := by
  unfold kdRe
  exact (MeasurePreserving.symm _ measurePreserving_prodAssoc_volume).comp
    (((MeasurePreserving.id volume).prod
      (measurePreserving_prodAssoc_volume.comp ((measurePreserving_prodComm_volume.prod (MeasurePreserving.id volume)).comp
        (MeasurePreserving.symm _ measurePreserving_prodAssoc_volume)))).comp measurePreserving_prodAssoc_volume)

def realCoordinatesSplitBySign (ε : Fin n → Bool) : (Fin n → ℝ) ≃ᵐ (Fin (pOf ε) → ℝ) × (Fin (qOf ε) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (kdIx ε)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (pOf ε) ⊕ Fin (qOf ε) => ℝ))

def complexCoordinatesSplitBySign (ε : Fin n → Bool) : (KPair ε → ℂ) ≃ᵐ
    ({ab : Fin (pOf ε) × Fin (pOf ε) // ab.2 < ab.1} → ℂ) × ({ab : Fin (qOf ε) × Fin (qOf ε) // ab.2 < ab.1} → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : KPair ε => ℂ) (kdPx ε)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ))

def kdT (ε : Fin n → Bool) : KCo ε ≃ᵐ UCo (pOf ε) × UCo (qOf ε) :=
  ((realCoordinatesSplitBySign ε).prodCongr (complexCoordinatesSplitBySign ε)).trans (kdRe _ _ _ _)

lemma kdT_fst (ε : Fin n → Bool) (w : KCo ε) : (kdT ε w).1 = kdCoS ε w true := rfl

lemma kdT_snd (ε : Fin n → Bool) (w : KCo ε) : (kdT ε w).2 = kdCoS ε w false := rfl

private lemma measurePreserving_realCoordinatesSplitBySign (ε : Fin n → Bool) : MeasurePreserving (realCoordinatesSplitBySign ε) volume volume := by
  unfold realCoordinatesSplitBySign
  exact (measurePreserving_sumPiEquivProdPi (fun _ => (volume : Measure ℝ))).comp
    (MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) (kdIx ε)))

private lemma measurePreserving_complexCoordinatesSplitBySign (ε : Fin n → Bool) : MeasurePreserving (complexCoordinatesSplitBySign ε) volume volume := by
  unfold complexCoordinatesSplitBySign
  exact (measurePreserving_sumPiEquivProdPi (fun _ => (volume : Measure ℂ))).comp
    (MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : KPair ε => (volume : Measure ℂ)) (kdPx ε)))

lemma kdT_mp (ε : Fin n → Bool) : MeasurePreserving (kdT ε) volume volume := by
  unfold kdT
  exact kdRe_mp.comp ((measurePreserving_realCoordinatesSplitBySign ε).prod (measurePreserving_complexCoordinatesSplitBySign ε))

section KDChart

open Set Topology

variable {N : ℕ}

def kdF (N : ℕ) (x : UCo N) : Fin N → Fin N → ℂ := Matrix.of.symm (NormedSpace.exp (skMat x))

lemma kd_skMat_injective : Function.Injective (skMat (N := N)) := by
  intro x y h
  have hd : ∀ a b, skMat x a b = skMat y a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · have := hd a a
    simp only [skMat, if_pos rfl] at this
    exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero this
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    have hab' : b < a := hab
    have := hd a b
    simp only [skMat, if_neg (ne_of_gt hab'), dif_pos hab'] at this
    exact this

lemma kd_continuous_skMat : Continuous (skMat (N := N)) := by
  refine continuous_matrix fun a b => ?_
  simp only [skMat]
  split_ifs
  · exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst))
  · exact (continuous_apply _).comp continuous_snd
  · exact ((continuous_apply _).comp continuous_snd).star.neg
  · exact continuous_const

lemma kd_skMat_zero : skMat (0 : UCo N) = 0 := by
  ext a b
  simp only [skMat]
  split_ifs <;> simp

lemma kd_exp_injOn {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] :
    ∃ V : Set 𝔸, IsOpen V ∧ (0 : 𝔸) ∈ V ∧ InjOn (NormedSpace.exp : 𝔸 → 𝔸) V := by
  have h : HasStrictFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℂ 𝔸 : 𝔸 ≃L[ℂ] 𝔸) : 𝔸 →L[ℂ] 𝔸) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  refine ⟨_, (h.toOpenPartialHomeomorph _).open_source, h.mem_toOpenPartialHomeomorph_source, ?_⟩
  have hi := (h.toOpenPartialHomeomorph _).injOn
  rwa [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at hi

lemma kd_exp_injOn_nhds : ∃ V : Set (Matrix (Fin N) (Fin N) ℂ), IsOpen V ∧ (0 : Matrix (Fin N) (Fin N) ℂ) ∈ V ∧
    InjOn (NormedSpace.exp : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) V := by
  letI : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  exact kd_exp_injOn

section KDCont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma kd_exp_continuous :
    Continuous (NormedSpace.exp : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) := by
  exact NormedSpace.exp_continuous

end KDCont

lemma continuous_kdF : Continuous (kdF N) := by
  exact kd_exp_continuous.comp kd_continuous_skMat

lemma kdF_injOn : ∃ r > 0, InjOn (kdF N) (Metric.ball 0 r) := by
  obtain ⟨V, hVo, hV0, hVi⟩ := kd_exp_injOn_nhds (N := N)
  have hU : IsOpen (skMat ⁻¹' V) := hVo.preimage kd_continuous_skMat
  have h0 : (0 : UCo N) ∈ skMat ⁻¹' V := by
    rw [Set.mem_preimage, kd_skMat_zero]
    exact hV0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨r, hr, fun x hx y hy hxy => kd_skMat_injective (hVi (hball hx) (hball hy) ?_)⟩
  exact hxy

end KDChart

end ReciprocityTheory.ChartRestriction.DS
