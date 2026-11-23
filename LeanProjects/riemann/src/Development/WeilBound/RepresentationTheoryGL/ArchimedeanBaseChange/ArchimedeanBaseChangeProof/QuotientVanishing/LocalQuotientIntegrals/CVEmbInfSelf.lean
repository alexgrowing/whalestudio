import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped ComplexOrder

namespace PositivityTheory.Rg.BcB.CV.LocalPlacePositivity

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cV_alg (v : InfinitePlace E) (x : E) : cV v (algebraMap E (Ad E) x) = v.embedding x :=
  pInf_algebraMap x v

open Classical in
theorem cV_embInf (v w : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV w) (embInf n v y) = if w = v then y else 1 := by
  ext i j
  change (GeneralLinearGroup.map (pInf E) (embInf n v y)) i j w = _
  unfold embInf
  rw [MonoidHom.comp_apply, pInf_infGL]
  change (MonoidHom.mulSingle (fun _ : InfinitePlace E => GL (Fin n) ℂ) v y w).val i j = _
  by_cases h : w = v
  · subst h
    simp
  · simp [h]

theorem cV_embInf_self (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV v) (embInf n v y) = y := by
  classical
  rw [cV_embInf, if_pos rfl]

theorem pFin_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (pFin E) (embInf n v y) = 1 := by
  unfold embInf
  exact pFin_infGL _

theorem cW_embInf (w : HeightOneSpectrum (𝓞 E)) (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cW w) (embInf n v y) = 1 := by
  have e : GeneralLinearGroup.map (cW w) (embInf n v y) =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (embInf n v y)) := rfl
  rw [e, pFin_embInf, map_one]

theorem cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d := by
  ext i j
  exact pInf_algebraMap (d i j) v

theorem map_inv_val {R : Type} [CommRing R] (f : Ad E →+* R) (x : GA E n) :
    ((x⁻¹ : GA E n).val).map f = ((GeneralLinearGroup.map f x)⁻¹ : GL (Fin n) R).val := by
  rw [← map_inv]; rfl

theorem frame_map_eq {R : Type} [CommRing R] (f : Ad E →+* R) (x y : GA E n)
    (h : GeneralLinearGroup.map f x = GeneralLinearGroup.map f y) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    (frame x M).map f = (frame y M).map f := by
  rw [frame, frame, Matrix.map_mul, Matrix.map_mul, map_inv_val, map_inv_val, h]

theorem frame_map (v : InfinitePlace E) (x : GA E n) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    (frame x M).map (cV v) = ((GeneralLinearGroup.map (cV v) x)⁻¹ : GL (Fin n) ℂ).val * M.map v.embedding := by
  have h : (M.map (algebraMap E (Ad E))).map (cV v) = M.map v.embedding := by
    ext i j
    exact cV_alg v (M i j)
  rw [frame, Matrix.map_mul, h, map_inv_val]

theorem lognInf_eq (v : InfinitePlace E) (x : GA E n) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    lognInf v (frame x M) = ploc (M.map v.embedding) (GeneralLinearGroup.map (cV v) x) := by
  rw [lognInf, frame_map, ploc]

theorem exists_ginv {K : Type} [Field K] {r m : ℕ} (A : Matrix (Fin r) (Fin m) K) :
    ∃ B : Matrix (Fin m) (Fin r) K, A * B * A = A := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.mulVecLin.rangeRestrict
    (LinearMap.range_rangeRestrict _)
  obtain ⟨h, hh⟩ := LinearMap.exists_extend g
  refine ⟨LinearMap.toMatrix' h, ?_⟩
  apply Matrix.mulVec_injective
  funext z
  have hz : A *ᵥ z ∈ LinearMap.range A.mulVecLin := ⟨z, rfl⟩
  have h1 : h (A *ᵥ z) = g ⟨A *ᵥ z, hz⟩ := LinearMap.congr_fun hh ⟨A *ᵥ z, hz⟩
  have h2 : A *ᵥ g ⟨A *ᵥ z, hz⟩ = A *ᵥ z :=
    congrArg Subtype.val (LinearMap.congr_fun hg ⟨A *ᵥ z, hz⟩)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, h1, h2]

theorem exists_left (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    ∃ L : Matrix (Fin (Module.finrank E W)) (Fin n) ℂ, L * (basisMat W).map v.embedding = 1 := by
  obtain ⟨B, hB⟩ := exists_ginv (basisMat W)
  have hinj : Function.Injective (basisMat W).mulVec := by
    refine Matrix.mulVec_injective_iff.2 ?_
    exact (Module.finBasis E W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hBM : B * basisMat W = 1 := by
    apply Matrix.mulVec_injective
    funext c
    apply hinj
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hB]
  refine ⟨B.map v.embedding, ?_⟩
  rw [← Matrix.map_mul, hBM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem gram_re_pos {r : ℕ} (B : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ) (hL : L * B = 1) :
    0 < (Bᴴ * B).det.re := by
  have hps : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have h0 : (Bᴴ * B).det ≠ 0 := by
    intro h
    obtain ⟨w, hw, hw0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    apply hw
    have h1 : B *ᵥ w = 0 := (conjTranspose_mul_self_mulVec_eq_zero B w).1 hw0
    calc w = (L * B) *ᵥ w := by rw [hL, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  have hpos : 0 < (Bᴴ * B).det := lt_of_le_of_ne hps.det_nonneg (Ne.symm h0)
  exact (Complex.pos_iff.1 hpos).1

theorem ploc_re_pos (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (g : GL (Fin n) ℂ) :
    0 < ((((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)ᴴ *
      ((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)).det).re := by
  obtain ⟨L, hL⟩ := exists_left v W
  refine gram_re_pos _ (L * g.val) ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, hL]

theorem ploc_cont (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    Continuous (ploc ((basisMat W).map v.embedding)) := by
  have hB : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding :=
    Units.continuous_coe_inv.matrix_mul continuous_const
  have hd : Continuous fun g : GL (Fin n) ℂ => ((((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)ᴴ *
      ((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)).det).re :=
    Complex.continuous_re.comp (hB.matrix_conjTranspose.matrix_mul hB).matrix_det
  exact (hd.log fun g => (ploc_re_pos v W g).ne').congr fun g => rfl

theorem ploc_mul_k {r : ℕ} (M : Matrix (Fin n) (Fin r) ℂ) (x k : GL (Fin n) ℂ) (hk : thC n k = k) :
    ploc M (x * k) = ploc M x := by
  have hk' : ((k⁻¹ : GL (Fin n) ℂ).val)ᴴ = k.val := by
    have h := congrArg Units.val hk
    rw [thetaR_val] at h
    refine Eq.trans ?_ h
    ext i j
    simp [Matrix.conjTranspose_apply]
  have e : ∀ B : Matrix (Fin n) (Fin r) ℂ,
      ((k⁻¹ : GL (Fin n) ℂ).val * B)ᴴ * ((k⁻¹ : GL (Fin n) ℂ).val * B) = Bᴴ * B := fun B => by
    rw [Matrix.conjTranspose_mul, hk', Matrix.mul_assoc, ← Matrix.mul_assoc k.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  unfold ploc
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, e]

theorem ploc_empty {r : ℕ} (M : Matrix (Fin n) (Fin r) ℂ) (hr : r = 0) (g : GL (Fin n) ℂ) : ploc M g = 0 := by
  subst hr
  simp [ploc]

theorem degM_empty {r : ℕ} (x : GA E n) (M : Matrix (Fin n) (Fin r) E) (hr : r = 0) : degM x M = 0 := by
  subst hr
  exact degM_zero x M

theorem deg_embInf (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (g : GL (Fin n) ℂ) (x : GA E n) :
    deg (embInf n v g * x) W + ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) =
      deg x W + ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x) := by
  classical
  have hfin : ∀ w, lognFin w (frame (embInf n v g * x) (basisMat W)) = lognFin w (frame x (basisMat W)) :=
    fun w => by
      unfold lognFin
      rw [frame_map_eq (cW w) _ x (by rw [map_mul, cW_embInf, one_mul])]
  have hinf : ∀ w, lognInf w (frame (embInf n v g * x) (basisMat W)) = lognInf w (frame x (basisMat W)) +
      if w = v then ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) -
        ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x) else 0 := fun w => by
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, lognInf_eq, lognInf_eq, map_mul, cV_embInf_self]
      ring
    · rw [if_neg h, add_zero]
      unfold lognInf
      rw [frame_map_eq (cV w) _ x (by rw [map_mul, cV_embInf, if_neg h, one_mul])]
  simp only [deg, degM, hfin, hinf, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

end PositivityTheory.Rg.BcB.CV.LocalPlacePositivity

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 in
theorem PositivityTheory.Rg.BcB.CV.pf_Ploc : PositivityTheory.Rg.BcB.CV.Ploc := by
  intro E _ _ _ n v W
  refine ⟨fun x => LocalPlacePositivity.lognInf_eq v x _, LocalPlacePositivity.ploc_cont v W, fun x k hk => LocalPlacePositivity.ploc_mul_k _ x k hk,
    fun hW => ?_, LocalPlacePositivity.cV_embInf_self v, fun v' hv' g => ?_, fun d => LocalPlacePositivity.cV_ratGL v d,
    fun g x => LocalPlacePositivity.deg_embInf v W g x⟩
  · subst hW
    exact ⟨fun x => LocalPlacePositivity.ploc_empty _ (by simp) x, fun x => LocalPlacePositivity.degM_empty x _ (by simp)⟩
  · classical
    rw [LocalPlacePositivity.cV_embInf, if_neg hv']
