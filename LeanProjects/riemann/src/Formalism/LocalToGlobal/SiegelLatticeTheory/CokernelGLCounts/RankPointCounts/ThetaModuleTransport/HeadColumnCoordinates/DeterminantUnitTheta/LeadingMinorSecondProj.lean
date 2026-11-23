import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ph_inverse (φ : E →+* F) {x : E} (hx : IsUnit x) : φ (Ring.inverse x) = (φ x)⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit, map_units_inv]

private theorem ph1_ph2_ZZm_apply (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (ZZm g Zh T T' a b) = (g.q : F)⁻¹ * ph1 g (Zh a b) ∧
      ph2 g (ZZm g Zh T T' a b) = -(g.q : F)⁻¹ * ph2 g (Zh b a) := by
  have hZ : ZZm g Zh T T' a b = g.e.symm ((g.e (Zh a b)).1 / (g.q : F), -((g.e (Zh b a)).2 / (g.q : F))) := by
    unfold ZZm cor
    simp only [HermSp.ZZplusOf, hs, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> simp
  have h1 : ∀ x : E, ph1 g x = (g.e x).1 := fun x => rfl
  have h2 : ∀ x : E, ph2 g x = (g.e x).2 := fun x => rfl
  rw [hZ, h1, h2, h1, h2, AlgEquiv.apply_symm_apply]
  constructor
  · simp only
    ring
  · simp only
    ring

theorem leadingMinor_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph1 g ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc).det =
      ((g.q : F)⁻¹) ^ r * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [RingHom.map_det, RingHom.map_det]
  have hmat : (ph1 g).mapMatrix ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc) =
      (g.q : F)⁻¹ • (ph1 g).mapMatrix (Zh.submatrix Fin.castSucc Fin.castSucc) := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      (ph1_ph2_ZZm_apply hs Zh T T' _ _).1]
  rw [hmat, Matrix.det_smul, Fintype.card_fin]

private theorem ph2_mapMatrix_ZZm_submatrix_eq_smul_transpose (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ph2 g).mapMatrix ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc) =
      (-(g.q : F)⁻¹) • Matrix.transpose ((ph2 g).mapMatrix (Zh.submatrix Fin.castSucc Fin.castSucc)) :=
  Matrix.ext fun a b => (ph1_ph2_ZZm_apply hs Zh T T' _ _).2

theorem leadingMinor_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph2 g ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc).det =
      (-(g.q : F)⁻¹) ^ r * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [RingHom.map_det, RingHom.map_det, ph2_mapMatrix_ZZm_submatrix_eq_smul_transpose hs Zh T T', Matrix.det_smul, Fintype.card_fin,
    Matrix.det_transpose]

theorem det_firstProj_zzMinus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph1 g (ZZm g Zh T T').det = ((g.q : F)⁻¹) ^ (r + 1) * ph1 g Zh.det := by
  rw [RingHom.map_det, RingHom.map_det]
  have hmat : (ph1 g).mapMatrix (ZZm g Zh T T') = (g.q : F)⁻¹ • (ph1 g).mapMatrix Zh := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      (ph1_ph2_ZZm_apply hs Zh T T' _ _).1]
  rw [hmat, Matrix.det_smul, Fintype.card_fin]

private theorem ph2_mapMatrix_ZZm_eq_smul_transpose (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ph2 g).mapMatrix (ZZm g Zh T T') = (-(g.q : F)⁻¹) • Matrix.transpose ((ph2 g).mapMatrix Zh) :=
  Matrix.ext fun a b => (ph1_ph2_ZZm_apply hs Zh T T' a b).2

theorem det_secondProj_zzMinus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph2 g (ZZm g Zh T T').det = (-(g.q : F)⁻¹) ^ (r + 1) * ph2 g Zh.det := by
  rw [RingHom.map_det, RingHom.map_det, ph2_mapMatrix_ZZm_eq_smul_transpose hs Zh T T', Matrix.det_smul, Fintype.card_fin,
    Matrix.det_transpose]

private theorem map_kapR_eq_inv_det_mul_det_submatrix (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (φ : E →+* F) (hu : IsUnit Zm.det) :
    φ (kapR Zm) = (φ Zm.det)⁻¹ * φ (Zm.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold kapR
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, ph_inverse φ hu,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hpow : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hpow, one_mul, Fin.succAbove_last]

private theorem isUnit_det_ZZm_of_isUnit_det (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) : IsUnit (ZZm g Zh T T').det := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have h1 : ph1 g Zh.det ≠ 0 := (hu.map (ph1 g)).ne_zero
  have h2 : ph2 g Zh.det ≠ 0 := (hu.map (ph2 g)).ne_zero
  rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff]
  constructor
  · show IsUnit (ph1 g (ZZm g Zh T T').det)
    rw [det_firstProj_zzMinus hs Zh T T']
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq)) h1)
  · show IsUnit (ph2 g (ZZm g Zh T T').det)
    rw [det_secondProj_zzMinus hs Zh T T']
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq))) h2)

theorem cornerRatio_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) :
    ph1 g (kapR (ZZm g Zh T T')) = (g.q : F) * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det /
      ph1 g Zh.det := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have h1 : ph1 g Zh.det ≠ 0 := (hu.map (ph1 g)).ne_zero
  rw [map_kapR_eq_inv_det_mul_det_submatrix _ _ (isUnit_det_ZZm_of_isUnit_det hs Zh T T' hu), det_firstProj_zzMinus hs Zh T T', leadingMinor_firstProj hs Zh T T', mul_inv, inv_pow,
    inv_inv, inv_pow, pow_succ]
  field_simp

theorem cornerRatio_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) :
    ph2 g (kapR (ZZm g Zh T T')) = -((g.q : F) * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det /
      ph2 g Zh.det) := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have h2 : ph2 g Zh.det ≠ 0 := (hu.map (ph2 g)).ne_zero
  have hc : (-(g.q : F)⁻¹) ≠ 0 := neg_ne_zero.2 (inv_ne_zero hq)
  have hcq : (-(g.q : F)⁻¹)⁻¹ = -(g.q : F) := by rw [inv_neg, inv_inv]
  rw [map_kapR_eq_inv_det_mul_det_submatrix _ _ (isUnit_det_ZZm_of_isUnit_det hs Zh T T' hu), det_secondProj_zzMinus hs Zh T T', leadingMinor_secondProj hs Zh T T', pow_succ, mul_inv,
    mul_inv, hcq]
  have hcr : (-(g.q : F)⁻¹) ^ r ≠ 0 := pow_ne_zero _ hc
  generalize (-(g.q : F)⁻¹) ^ r = C at hcr ⊢
  field_simp

theorem laG_llMap (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : M.Mat (r + 1)) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det)
    (TT : M.R) (m : Fin (r + 1) → M.R) :
    laG (ZZm g Zh T T') (llMap hs Z TT m) =
      (m (Fin.last r) : E) * (1 - tau0 g T T' * kapR (ZZm g Zh T T')) -
        (TT : E) * algebraMap F E (trO hs (m (Fin.last r))) * kapR (ZZm g Zh T T') := by
  have hl : ∀ v w : Fin (r + 1) → M.R, laG (ZZm g Zh T T') (v - w) =
      laG (ZZm g Zh T T') v - laG (ZZm g Zh T T') w := by
    intro v w
    unfold laG
    rw [show (fun i => ((v - w) i : E)) = (fun i => (v i : E)) - (fun i => (w i : E)) by
      funext i; simp, Matrix.mulVec_sub]
    rfl
  have hsm : ∀ (c : M.R) (v : Fin (r + 1) → M.R), laG (ZZm g Zh T T') (c • v) =
      (c : E) * laG (ZZm g Zh T T') v := by
    intro c v
    unfold laG
    rw [show (fun i => ((c • v) i : E)) = (c : E) • (fun i => (v i : E)) by
      funext i; simp, Matrix.mulVec_smul]
    rfl
  show laG _ (Z.Z.mulVec m - (TT * dgR hs (trO hs (m (Fin.last r)))) • eV r) = _
  rw [hl, hsm, laG_mulVec Zh T T' Z hZ (unit_zzm hs Zh T T' hu), laG_e]
  rw [Subring.coe_mul, dgR_coe]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
