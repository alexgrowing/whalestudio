import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FiltrationTheoremOfClauses
import Formalism.GradedWeylDivisibility.FinalB

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

variable {n : ℕ}

lemma qd_evGLR_mapCoord {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (z : GLCoord ℤ n) :
    evGLR (R := ℚ) x (mapCoord ℚ z) = evGL x z := by
  have h : (evGLR (R := ℚ) x).comp (mapCoord ℚ) = evGL x := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGLR, mapCoord, evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h

def qd_sig (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ →ₐ[ℚ] GLCoord ℚ n :=
  (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)).comp (rename Prod.swap)

lemma qd_sig_X (v : Fin n × Fin n) :
    qd_sig n (X v) = algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (v.2, v.1)) := by
  simp [qd_sig, Prod.swap]

lemma qd_genDet_ne (n : ℕ) : (genMat ℚ n).det ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)) h
  rw [RingHom.map_det] at this
  have h1 : (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)).mapMatrix (genMat ℚ n)
      = 1 := by
    ext a b; simp [genMat, Matrix.one_apply]
  rw [h1] at this
  simp at this

lemma qd_sig_inj (n : ℕ) : Function.Injective (qd_sig n) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)) :=
    IsLocalization.injective (GLCoord ℚ n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (qd_genDet_ne n))
  have h2 : Function.Injective (rename (R := ℚ) (Prod.swap : Fin n × Fin n → Fin n × Fin n)) :=
    rename_injective _ Prod.swap_injective
  intro p q hpq
  exact h2 (h1 hpq)

lemma qd_ev_sig {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) x (qd_sig n P) = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) P := by
  have h : (evGLR (R := ℚ) x).comp (qd_sig n).toRingHom
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [qd_sig, evGLR, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ P) h

lemma qd_evGL_detU {R : Type} [CommRing R] (x : GL (Fin n) R) (m : ℤ) :
    evGL x ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((Matrix.GeneralLinearGroup.det x ^ m : Rˣ) : R) := by
  have h : Units.map (evGL x).toMonoidHom (detU n) = Matrix.GeneralLinearGroup.det x := by
    ext
    simp only [Units.coe_map, detU, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    rw [evGL, IsLocalization.Away.lift_eq, RingHom.map_det, genMat_map_eval]
  rw [← h, ← map_zpow]
  rfl

variable [NeZero n]

def qd_P (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ c : ↥(TCols mu), initMinor ℚ (fun p => (I c).1.orderEmbOfFin (I c).2 p) (colH_le mu c)

def qd_U (mu : Fin n → ℤ) : GLCoord ℚ n := mapCoord ℚ ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)

lemma qd_can_emb (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2 (f := Fin.castLE (colH_le mu c))
    (by intro x; simp [canT]) (Fin.strictMono_castLE _)
  rw [← this]

lemma qd_brk (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord ℚ (brk mu I) = qd_U mu * qd_sig n (qd_P mu I) := by
  unfold brk TMat qd_U qd_P
  rw [map_mul, map_prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold minorC initMinor
  rw [mapCoord, IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.map_det, AlgHom.map_det,
    RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [genMat, qd_can_emb, qd_sig_X]

def qd_nu (mu : Fin n → ℤ) : Fin n → ℕ := ∑ c : ↥(TCols mu), initW n (colH mu c)

lemma qd_nu_anti (mu : Fin n → ℤ) : Antitone (qd_nu mu) := by
  intro s t hst
  unfold qd_nu
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_le_sum fun c _ => ?_
  have : s.val ≤ t.val := hst
  unfold initW
  split_ifs <;> omega

lemma tableauBideterminant_mem_dualWeyl' (mu : Fin n → ℤ) (I : TIdx mu) : qd_P mu I ∈ dualWeyl ℚ n n (qd_nu mu) :=
  dualWeyl_prod univ _ _ (fun _ _ => initMinor_mem _ _)

def qd_L (mu : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] GLCoord ℚ n :=
  (LinearMap.mulLeft ℚ (qd_U mu)) ∘ₗ (qd_sig n).toLinearMap

lemma qd_L_apply (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    qd_L mu P = qd_U mu * qd_sig n P := rfl

lemma qd_L_P (mu : Fin n → ℤ) (I : TIdx mu) : qd_L mu (qd_P mu I) = mapCoord ℚ (brk mu I) :=
  (qd_brk mu I).symm

lemma qd_span_le (mu : Fin n → ℤ) :
    Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)) ≤
      (dualWeyl ℚ n n (qd_nu mu)).map (qd_L mu) := by
  rw [Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  exact ⟨qd_P mu I, tableauBideterminant_mem_dualWeyl' mu I, qd_L_P mu I⟩

omit [NeZero n] in
lemma generic_point_det_isUnit (n : ℕ) : IsUnit (Matrix.of fun a b : Fin n =>
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))).det := by
  have : (Matrix.of fun a b : Fin n =>
      Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))) =
      (Polynomial.C.comp (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))).mapMatrix (genMat ℚ n) := by
    ext a b : 2; simp [genMat]
  rw [this, ← RingHom.map_det]
  exact (IsLocalization.Away.algebraMap_isUnit (S := GLCoord ℚ n) (genMat ℚ n).det).map Polynomial.C

def qd_genPt (n : ℕ) : GL (Fin n) (Polynomial (GLCoord ℚ n)) :=
  Matrix.GeneralLinearGroup.mk'' _ (generic_point_det_isUnit n)

omit [NeZero n] in
lemma qd_genPt_val (i j : Fin n) : (qd_genPt n).val i j =
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (i, j))) := rfl

def qd_trans {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) : GL (Fin n) R :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection a b t)
    (by rw [Matrix.det_transvection_of_ne _ _ hab]; exact isUnit_one)

omit [NeZero n] in
lemma qd_trans_det {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) :
    Matrix.GeneralLinearGroup.det (qd_trans a b hab t) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transvection_of_ne _ _ hab t

omit [NeZero n] in
lemma qd_mul_trans {R : Type} [CommRing R] (x : GL (Fin n) R) (a b : Fin n) (hab : a ≠ b) (t : R) (i j : Fin n) :
    (x * qd_trans a b hab t).val i j = x.val i j + if j = b then t * x.val i a else 0 := by
  have : (x * qd_trans a b hab t).val = x.val * Matrix.transvection a b t := rfl
  rw [this]
  split_ifs with h
  · subst h; rw [Matrix.mul_transvection_apply_same]
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ h, add_zero]

omit [NeZero n] in
lemma qd_trans_diag {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) (i : Fin n) :
    (qd_trans a b hab t).val i i = 1 := by
  have : (qd_trans a b hab t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, h⟩; exact hab h.symm), add_zero]

omit [NeZero n] in
lemma qd_trans_low {R : Type} [CommRing R] (a b : Fin n) (hab : a < b) (t : R) (i j : Fin n) (hji : j < i) :
    (qd_trans a b hab.ne t).val i j = 0 := by
  have : (qd_trans a b hab.ne t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr hji.le)), add_zero]

omit [NeZero n] in
lemma aeval_generic_point (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1) P = Polynomial.C (qd_sig n P) := by
  have h : (aeval (R := ℚ) (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1))
      = (Polynomial.CAlgHom (R := ℚ) (A := GLCoord ℚ n)).comp (qd_sig n) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h

omit [NeZero n] in
lemma qd_aeval_xu (a b : Fin n) (hab : a ≠ b) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1) P
      = Polynomial.map (qd_sig n).toRingHom (rowGen ℚ a b P) := by
  have h : (aeval (R := ℚ)
      (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1))
      = (Polynomial.mapAlgHom (qd_sig n)).comp (rowGen ℚ a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [aeval_X, AlgHom.comp_apply, rowGen_X, qd_mul_trans, Polynomial.coe_mapAlgHom]
    split_ifs <;> simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h

lemma qd_U_unit {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (mu : Fin n → ℤ) :
    IsUnit (evGLR (R := ℚ) x (qd_U mu)) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGL_detU]
  exact Units.isUnit _

lemma qd_U_inv {R' : Type} [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R') (mu : Fin n → ℤ)
    (hu : Matrix.GeneralLinearGroup.det u = 1) :
    evGLR (R := ℚ) (x * u) (qd_U mu) = evGLR (R := ℚ) x (qd_U mu) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, map_mul, hu, mul_one]

lemma qd_raise (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) (a b : Fin n) (hab : a ≠ b)
    (h : evGLR (R := ℚ) (qd_genPt n * qd_trans a b hab Polynomial.X) (qd_L mu P)
      = evGLR (R := ℚ) (qd_genPt n) (qd_L mu P)) :
    rowGen ℚ a b P = Polynomial.C P := by
  rw [qd_L_apply, map_mul, map_mul, qd_U_inv _ _ _ (qd_trans_det a b hab _)] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, qd_aeval_xu] at h2
  apply Polynomial.map_injective (qd_sig n).toRingHom (qd_sig_inj n)
  rw [h2, Polynomial.map_C]
  rfl

lemma tableauBideterminant_canonical_eq_prod_leadingMinor (mu : Fin n → ℤ) :
    qd_P mu (canT mu) = ∏ c : ↥(TCols mu), lpMinor ℚ (colH mu c) (colH_le mu c) (colH_le mu c) := by
  unfold qd_P
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor lpMinor
  simp only [qd_can_emb]

lemma tableauBideterminant_canonical_eq_smul_highestWeight (mu : Fin n → ℤ) : ∃ c0 : ℚ, c0 ≠ 0 ∧ qd_P mu (canT mu) = c0 • hw ℚ le_rfl (qd_nu mu) := by
  obtain ⟨c0, h0⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ (tableauBideterminant_mem_dualWeyl' mu (canT mu)) (by
    intro a b hab k hk
    unfold rowDiv
    rw [tableauBideterminant_canonical_eq_prod_leadingMinor, map_prod]
    simp only [rowGen_lpMinor ℚ a b hab]
    rw [← map_prod, Polynomial.coeff_C, if_neg (by omega)])
  refine ⟨c0, ?_, h0⟩
  rintro rfl
  rw [zero_smul, tableauBideterminant_canonical_eq_prod_leadingMinor] at h0
  have := congrArg (eval (idPoint ℚ n n)) h0
  simp [eval_idPoint_lpMinor] at this

theorem eq_smul_canonical_of_unipotent_invariant (mu : Fin n → ℤ) (f : GLCoord ℚ n)
    (hf : f ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)))
    (hinv : ∀ (R' : Type) [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R'), (∀ a, u.val a a = 1) →
      (∀ a b, b < a → u.val a b = 0) → evGLR (R := ℚ) (x * u) f = evGLR (R := ℚ) x f) :
    ∃ c : ℚ, f = c • mapCoord ℚ (brk mu (canT mu)) := by
  obtain ⟨P, hP, rfl⟩ := qd_span_le mu hf
  obtain ⟨c, hc⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) P hP (by
    intro a b hab k hk
    unfold rowDiv
    rw [qd_raise mu P a b hab.ne (hinv _ _ _ (qd_trans_diag a b hab.ne _) (qd_trans_low a b hab _)),
      Polynomial.coeff_C, if_neg (by omega)])
  obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
  refine ⟨c / c0, ?_⟩
  rw [← qd_L_P, ← map_smul, h0, hc, smul_smul, div_mul_cancel₀ _ hc0]

end Formalism.InvariantFactorPaths.ColumnFamilies
