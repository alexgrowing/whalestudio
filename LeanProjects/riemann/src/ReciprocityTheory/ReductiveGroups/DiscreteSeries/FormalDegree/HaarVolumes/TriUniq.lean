import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaar

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

namespace PositiveTriangularSet

theorem triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  rcases t with ⟨d, u⟩
  refine Prod.ext ?_ ?_
  · funext j; simp [triCoOf, upMat]
  · funext ab; simp [triCoOf, upMat, ab.2.ne, ab.2]

theorem upMat_up (t : TriCo N) : (upMat t).BlockTriangular id := by
  intro i j h
  have h' : j < i := h
  simp [upMat, h'.ne', not_lt.mpr h'.le]

theorem upMat_diag (t : TriCo N) (j : Fin N) : upMat t j j = ((t.1 j : ℝ) : ℂ) := by
  simp [upMat]

theorem upMat_triCoOf_of_up (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.BlockTriangular id)
    (hd : ∀ j, (A j j).im = 0) : upMat (triCoOf A) = A := by
  ext i j
  simp only [upMat, triCoOf]
  split_ifs with h1 h2
  · subst h1; exact Complex.ext (by simp) (by simp [hd])
  · rfl
  · have : j < i := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    exact (@hA i j this).symm

theorem diag_mul_of_up {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (j : Fin N) : (A * B) j j = A j j * B j j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [@hA j k h, zero_mul]
  · rw [@hB k j h, mul_zero]

theorem isOpen_triPos : IsOpen (triPos N) := by
  have : triPos N = ⋂ j : Fin N, {t : TriCo N | 0 < t.1 j} := by ext; simp [triPos]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const ((continuous_apply j).comp continuous_fst)

theorem ms_triPos : MeasurableSet (triPos N) := isOpen_triPos.measurableSet

theorem continuous_upMat : Continuous (upMat : TriCo N → Matrix (Fin N) (Fin N) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [upMat]
  split_ifs
  · exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

theorem continuous_triCoOf : Continuous (triCoOf : Matrix (Fin N) (Fin N) ℂ → TriCo N) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun ab => ?_)
  · exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply j))
  · exact (continuous_apply _).comp (continuous_apply _)

theorem det_upMat (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [det_of_isUpperTriangular (upMat_up t)]
  simp [upMat_diag]

theorem det_upMat_ne (t : TriCo N) (ht : t ∈ triPos N) : IsUnit (upMat t).det := by
  rw [det_upMat, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro j _
  exact Complex.ofReal_ne_zero.mpr (ht j).ne'

theorem inv_up (t : TriCo N) (ht : t ∈ triPos N) : (upMat t)⁻¹.BlockTriangular id := by
  let _ := (upMat t).invertibleOfIsUnitDet (det_upMat_ne t ht)
  exact blockTriangular_inv_of_blockTriangular (upMat_up t)

theorem inv_diag (t : TriCo N) (ht : t ∈ triPos N) (j : Fin N) :
    (upMat t)⁻¹ j j = (((t.1 j)⁻¹ : ℝ) : ℂ) := by
  have h1 := congrFun (congrFun (nonsing_inv_mul _ (det_upMat_ne t ht)) j) j
  rw [diag_mul_of_up (inv_up t ht) (upMat_up t), upMat_diag, Matrix.one_apply_eq] at h1
  have h2 : ((t.1 j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ht j).ne'
  rw [Complex.ofReal_inv]
  exact eq_inv_of_mul_eq_one_left h1

theorem upMat_mul_mem (a b : TriCo N) (ha : a ∈ triPos N) (hb : b ∈ triPos N) :
    upMat (triCoOf (upMat a * upMat b)) = upMat a * upMat b ∧
      triCoOf (upMat a * upMat b) ∈ triPos N := by
  have hu := (upMat_up a).mul (upMat_up b)
  have hd : ∀ j, (upMat a * upMat b) j j = (((a.1 j * b.1 j : ℝ)) : ℂ) := fun j => by
    rw [diag_mul_of_up (upMat_up a) (upMat_up b), upMat_diag, upMat_diag, Complex.ofReal_mul]
  refine ⟨upMat_triCoOf_of_up _ hu (fun j => by rw [hd]; simp), fun j => ?_⟩
  show 0 < ((upMat a * upMat b) j j).re
  rw [hd, Complex.ofReal_re]
  exact mul_pos (ha j) (hb j)

theorem upMat_inv_mem (a : TriCo N) (ha : a ∈ triPos N) :
    upMat (triCoOf (upMat a)⁻¹) = (upMat a)⁻¹ ∧ triCoOf (upMat a)⁻¹ ∈ triPos N := by
  refine ⟨upMat_triCoOf_of_up _ (inv_up a ha) (fun j => by rw [inv_diag a ha]; simp), fun j => ?_⟩
  show 0 < ((upMat a)⁻¹ j j).re
  rw [inv_diag a ha, Complex.ofReal_re]
  exact inv_pos.mpr (ha j)

theorem one_mem : upMat (triCoOf (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 ∧
    triCoOf (1 : Matrix (Fin N) (Fin N) ℂ) ∈ triPos N := by
  refine ⟨upMat_triCoOf_of_up _ Matrix.blockTriangular_one (fun j => by simp), fun j => ?_⟩
  show 0 < ((1 : Matrix (Fin N) (Fin N) ℂ) j j).re
  simp

abbrev TG (N : ℕ) : Type := ↥(triPos N)

scoped instance : Mul (TG N) := ⟨fun a b => ⟨triCoOf (upMat b.1 * upMat a.1), (upMat_mul_mem b.1 a.1 b.2 a.2).2⟩⟩
scoped instance : One (TG N) := ⟨⟨triCoOf 1, one_mem.2⟩⟩
scoped instance : Inv (TG N) := ⟨fun a => ⟨triCoOf (upMat a.1)⁻¹, (upMat_inv_mem a.1 a.2).2⟩⟩

theorem tg_mul_val (a b : TG N) : (a * b).1 = triCoOf (upMat b.1 * upMat a.1) := rfl

theorem upMat_tg_mul (a b : TG N) : upMat (a * b).1 = upMat b.1 * upMat a.1 :=
  (upMat_mul_mem b.1 a.1 b.2 a.2).1

theorem upMat_tg_one : upMat (1 : TG N).1 = 1 := one_mem.1

theorem upMat_tg_inv (a : TG N) : upMat a⁻¹.1 = (upMat a.1)⁻¹ := (upMat_inv_mem a.1 a.2).1

theorem tg_ext {a b : TG N} (h : upMat a.1 = upMat b.1) : a = b := by
  apply Subtype.ext
  rw [← triCoOf_upMat a.1, ← triCoOf_upMat b.1, h]

scoped instance : Group (TG N) where
  mul_assoc a b c := tg_ext (by simp only [upMat_tg_mul, Matrix.mul_assoc])
  one_mul a := tg_ext (by rw [upMat_tg_mul, upMat_tg_one, Matrix.mul_one])
  mul_one a := tg_ext (by rw [upMat_tg_mul, upMat_tg_one, Matrix.one_mul])
  inv_mul_cancel a := tg_ext (by
    rw [upMat_tg_mul, upMat_tg_inv, upMat_tg_one, mul_nonsing_inv _ (det_upMat_ne a.1 a.2)])

theorem continuous_tg_mul : Continuous fun p : TG N × TG N => p.1 * p.2 :=
  Continuous.subtype_mk (continuous_triCoOf.comp
    ((continuous_upMat.comp (continuous_subtype_val.comp continuous_snd)).matrix_mul
      (continuous_upMat.comp (continuous_subtype_val.comp continuous_fst)))) _

theorem continuous_tg_inv : Continuous fun a : TG N => a⁻¹ := by
  refine Continuous.subtype_mk (continuous_triCoOf.comp ?_) _
  rw [continuous_iff_continuousAt]
  intro a
  have hd : (upMat a.1).det ≠ 0 := (det_upMat_ne a.1 a.2).ne_zero
  have hinv : ContinuousAt Ring.inverse (upMat a.1).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd
  exact (continuousAt_matrix_inv (upMat a.1) hinv).comp (f := fun x : TG N => upMat x.1)
    (continuous_upMat.comp continuous_subtype_val).continuousAt

scoped instance : IsTopologicalGroup (TG N) where
  continuous_mul := continuous_tg_mul
  continuous_inv := continuous_tg_inv

scoped instance : LocallyCompactSpace (TG N) := isOpen_triPos.locallyCompactSpace

theorem continuous_rmul (g : TriCo N) : Continuous fun t : TriCo N => triCoOf (upMat t * upMat g) :=
  continuous_triCoOf.comp (continuous_upMat.matrix_mul continuous_const)

theorem lift_inv (κ : Measure (TriCo N)) (hκ0 : κ (triPos N)ᶜ = 0)
    (hinv : ∀ t0 ∈ triPos N, Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) κ = κ) :
    (κ.comap Subtype.val : Measure (TG N)).IsMulLeftInvariant := by
  constructor
  intro g
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA, comap_subtype_coe_apply ms_triPos,
    comap_subtype_coe_apply ms_triPos]
  have key : Subtype.val '' ((fun x : TG N => g * x) ⁻¹' A) =
      (fun t : TriCo N => triCoOf (upMat t * upMat g.1)) ⁻¹' (Subtype.val '' A) ∩ triPos N := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨g * x, hx, rfl⟩, x.2⟩
    · rintro ⟨⟨y, hy, hyt⟩, ht⟩
      refine ⟨⟨t, ht⟩, ?_, rfl⟩
      have : g * ⟨t, ht⟩ = y := Subtype.ext (by rw [hyt]; rfl)
      show g * ⟨t, ht⟩ ∈ A
      rw [this]; exact hy
  rw [key, measure_inter_conull hκ0, ← Measure.map_apply (continuous_rmul g.1).measurable
    (MeasurableSet.subtype_image ms_triPos hA), hinv g.1 g.2]

theorem lift_fin (κ : Measure (TriCo N))
    (hfin : ∀ K : Set (TriCo N), IsCompact K → K ⊆ triPos N → κ K < ⊤) :
    IsFiniteMeasureOnCompacts (κ.comap Subtype.val : Measure (TG N)) :=
  ⟨fun K hK => by
    rw [comap_subtype_coe_apply ms_triPos]
    exact hfin _ (hK.image continuous_subtype_val) (by rintro _ ⟨x, -, rfl⟩; exact x.2)⟩

theorem restore (κ : Measure (TriCo N)) (hκ0 : κ (triPos N)ᶜ = 0) :
    (κ.comap Subtype.val : Measure (TG N)).map Subtype.val = κ := by
  rw [map_comap_subtype_coe ms_triPos]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hκ0)

theorem triMeas_compl : triMeas N (triPos N)ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply ms_triPos.compl]
  simp

theorem triDens_pos (t : TriCo N) (ht : t ∈ triPos N) : triDens t ≠ 0 := by
  unfold triDens
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Finset.prod_pos fun j _ => zpow_pos (ht j) _

theorem triMeas_ne_zero : triMeas N ≠ 0 := by
  intro h0
  have h1 : triMeas N (triPos N) = 0 := by rw [h0]; rfl
  unfold triMeas at h1
  have haem : AEMeasurable triDens (volume.restrict (triPos N)) := by
    refine ContinuousOn.aemeasurable ?_ ms_triPos
    refine ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_finsetProd _ fun j _ => ?_)
    exact ContinuousOn.zpow₀ ((continuous_apply j).comp continuous_fst).continuousOn _
      (fun t ht => Or.inl (ht j).ne')
  rw [withDensity_apply _ ms_triPos, Measure.restrict_restrict ms_triPos, Set.inter_self,
    setLIntegral_eq_zero_iff' ms_triPos haem] at h1
  have h2 := ae_iff.mp h1
  have h3 : {x | ¬(x ∈ triPos N → triDens x = 0)} = triPos N := by
    ext x
    constructor
    · intro h
      by_contra hx
      exact h (fun h' => absurd h' hx)
    · intro h h'
      exact triDens_pos x h (h' h)
  rw [h3] at h2
  exact isOpen_triPos.measure_ne_zero volume ⟨(fun _ => 1, 0), fun j => one_pos⟩ h2

end PositiveTriangularSet

open PositiveTriangularSet in
theorem triMeas_unique (κ : Measure (TriCo N)) (hκ0 : κ (triPos N)ᶜ = 0)
    (hfin : ∀ K : Set (TriCo N), IsCompact K → K ⊆ triPos N → κ K < ⊤)
    (hinv : ∀ t0 ∈ triPos N, Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) κ = κ) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ κ = c • triMeas N := by
  have := lift_inv κ hκ0 hinv
  have := lift_fin κ hfin
  have := lift_inv (triMeas N) triMeas_compl (fun t0 h => triMeas_map_mul_right t0 h)
  have := lift_fin (triMeas N) (fun K hK h => triMeas_compact_lt_top K hK h)
  obtain ⟨a, h1⟩ : ∃ a : NNReal, (κ.comap Subtype.val : Measure (TG N)) = a • Measure.haar :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨b, h2⟩ : ∃ b : NNReal, ((triMeas N).comap Subtype.val : Measure (TG N)) = b • Measure.haar :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  set η : Measure (TriCo N) := (Measure.haar : Measure (TG N)).map Subtype.val
  have hk : κ = (a : ENNReal) • η := by
    rw [← restore κ hκ0, h1, ENNReal.smul_def, Measure.map_smul]
  have ht : triMeas N = (b : ENNReal) • η := by
    rw [← restore (triMeas N) triMeas_compl, h2, ENNReal.smul_def, Measure.map_smul]
  have hb : b ≠ 0 := by
    rintro hb0
    apply triMeas_ne_zero (N := N)
    rw [ht, hb0]; simp
  refine ⟨((a / b : NNReal) : ENNReal), ENNReal.coe_ne_top, ?_⟩
  rw [ht, smul_smul, ← ENNReal.coe_mul, div_mul_cancel₀ a hb, hk]

end ReciprocityTheory.ChartRestriction.DS
