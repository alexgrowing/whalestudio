import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def ph1 (g : SplitG M.L) : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def ph2 (g : SplitG M.L) : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

theorem firstProj_apply (x : E) : ph1 g x = (g.e x).1 := rfl
theorem secondProj_apply (x : E) : ph2 g x = (g.e x).2 := rfl

theorem isUnit_iff_ph (x : E) : IsUnit x ↔ ph1 g x ≠ 0 ∧ ph2 g x ≠ 0 := by
  rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  rfl

theorem eq_iff_ph (x y : E) : x = y ↔ ph1 g x = ph1 g y ∧ ph2 g x = ph2 g y := by
  rw [← g.e.injective.eq_iff, Prod.ext_iff]
  rfl

abbrev tau0 (g : SplitG M.L) (T T' : F) : E := g.e.symm (-T / (g.q : F), T' / (g.q : F))

theorem zzMinus_firstProj_smul (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (ph1 g) = (g.q : F)⁻¹ • Zh.map (ph1 g) := by
  unfold ZZm HermSp.ZZplusOf
  rw [hs]
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, firstProj_apply, cor]
  split_ifs <;> simp [div_eq_inv_mul]

theorem zzMinus_secondProj_transpose (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (ph2 g) = (-(g.q : F)⁻¹) • (Zh.map (ph2 g)).transpose := by
  unfold ZZm HermSp.ZZplusOf
  rw [hs]
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, secondProj_apply, cor,
    Matrix.transpose_apply]
  split_ifs <;> simp [div_eq_inv_mul]

theorem det_ph {n : Type} [Fintype n] [DecidableEq n] (φ : E →+* F) (A : Matrix n n E) :
    φ A.det = (A.map φ).det := by
  exact RingHom.map_det φ A

theorem unit_zzm (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) : IsUnit (ZZm g Zh T T').det := by
  have hq : (g.q : F) ≠ 0 := by exact_mod_cast g.q_irr.ne_zero
  rw [isUnit_iff_ph (g := g)] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  constructor
  · rw [det_ph, zzMinus_firstProj_smul hs, Matrix.det_smul, ← det_ph]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq)) h1
  · rw [det_ph, zzMinus_secondProj_transpose hs, Matrix.det_smul, Matrix.det_transpose, ← det_ph]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero hq))) h2

theorem zzm_eq (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') :
    ZZm g Zh T T' = Z.Z.map M.R.subtype + Matrix.of fun a b => cor r a b (tau0 g T T') := by
  unfold ZZm
  rw [← hZ]

abbrev kapR (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := Zm⁻¹ (Fin.last r) (Fin.last r)

theorem laG_mulVec (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit (ZZm g Zh T T').det)
    (m : Fin (r + 1) → M.R) :
    laG (ZZm g Zh T T') (Z.Z.mulVec m) =
      (m (Fin.last r) : E) * (1 - tau0 g T T' * kapR (ZZm g Zh T T')) := by
  unfold laG
  have hcoe : (fun i => ((Z.Z.mulVec m i : M.R) : E)) = (Z.Z.map M.R.subtype).mulVec (fun j => (m j : E)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [hcoe]
  have hZ' : Z.Z.map M.R.subtype = ZZm g Zh T T' - Matrix.of fun a b => cor r a b (tau0 g T T') := by
    rw [zzm_eq (g := g) Zh T T' Z hZ, add_sub_cancel_right]
  have hC : (Matrix.of fun a b => cor r a b (tau0 g T T')).mulVec (fun j => (m j : E)) =
      Pi.single (Fin.last r) (tau0 g T T' * (m (Fin.last r) : E)) := by
    funext i
    by_cases h : i = Fin.last r <;> simp [Matrix.mulVec, dotProduct, cor, h]
  rw [hZ', Matrix.sub_mulVec, hC, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec, Matrix.mulVec_single]
  simp only [Pi.sub_apply, Pi.smul_apply, Matrix.col_apply, op_smul_eq_mul]
  unfold kapR
  ring

theorem laG_e (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    laG Zm (eV (M := M) r) = kapR Zm := by
  unfold laG eV
  have e : (fun i => (((Pi.single (Fin.last r) (1 : M.R) : Fin (r + 1) → M.R) i : M.R) : E)) =
      (Pi.single (Fin.last r) (1 : E) : Fin (r + 1) → E) := by
    funext i
    by_cases h : i = Fin.last r <;> simp [h]
  rw [e, Matrix.mulVec_single]
  simp [kapR]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
