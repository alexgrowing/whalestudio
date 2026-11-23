import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.EqSmulCanonicalOfUnipotentInvariant
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLDetUZpow
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qd_vander {σ : Type} (W : Submodule ℚ (MvPolynomial σ ℚ)) (p : Polynomial (MvPolynomial σ ℚ))
    (h : ∀ t : ℕ, p.eval (C (t : ℚ)) ∈ W) (k : ℕ) : p.coeff k ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  set ψ : MvPolynomial σ ℚ →ₗ[ℚ] ℚ := φ ∘ₗ W.mkQ with hψ
  have hW : ∀ x ∈ W, ψ x = 0 := by
    intro x hx
    rw [hψ, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hx, map_zero]
  set q : Polynomial ℚ := ∑ i ∈ range (p.natDegree + 1), Polynomial.monomial i (ψ (p.coeff i)) with hq
  have hev : ∀ t : ℕ, q.eval (t : ℚ) = 0 := by
    intro t
    rw [← hW _ (h t), Polynomial.eval_eq_sum_range (p := p), map_sum, hq, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (p.coeff i), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun t : ℕ => (t : ℚ)))
    · rintro _ ⟨t, rfl⟩
      exact hev t
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have hc : q.coeff k = ψ (p.coeff k) := by
    rw [hq, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' ]
    split_ifs with hk
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk), map_zero]
  rw [hq0, Polynomial.coeff_zero] at hc
  exact hc.symm

variable {n : ℕ}

lemma qd_eval_rowGen (a b : Fin n) (t : ℚ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (rowGen ℚ a b f).eval (C t) = rowAct ℚ (1 + Matrix.single b a t) f := by
  have h : ((Polynomial.aeval (R := MvPolynomial (Fin n × Fin n) ℚ) (C t : MvPolynomial (Fin n × Fin n) ℚ)).restrictScalars
      ℚ).comp (rowGen ℚ a b) = rowAct ℚ (1 + Matrix.single b a t) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowGen_X, rowAct, aeval_X]
    simp only [AlgHom.restrictScalars_apply, map_add, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Matrix.single_apply]
    congr 1
    · simp
    · split_ifs with hv
      · simp only [hv, true_and, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
        simp
      · simp [Ne.symm hv]
  have := congrArg (fun φ => φ f) h
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using this

lemma qd_det_E (a b : Fin n) (t : ℕ) : IsUnit (1 + Matrix.single b a (t : ℚ)).det := by
  by_cases hab : b = a
  · subst hab
    have : (1 + Matrix.single b b (t : ℚ)) = Matrix.diagonal (fun i => if i = b then (1 + t : ℚ) else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = b <;> simp [hi, Matrix.single_apply]
        intro h; exact absurd h.symm hi
      · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [this, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp only [mem_univ, if_true]
    exact isUnit_iff_ne_zero.2 (by positivity)
  · have : (1 + Matrix.single b a (t : ℚ)) = Matrix.transvection b a (t : ℚ) := rfl
    rw [this, Matrix.det_transvection_of_ne _ _ hab]
    exact isUnit_one

variable [NeZero n]

def translatesSpanCanonical (mu : Fin n → ℤ) : Submodule ℚ (MvPolynomial (Fin n × Fin n) ℚ) :=
  Submodule.span ℚ {f | ∃ g : Matrix (Fin n) (Fin n) ℚ, IsUnit g.det ∧ f = rowAct ℚ g (qd_P mu (canT mu))}

lemma qd_W_closed (mu : Fin n → ℤ) : RowDivClosed (translatesSpanCanonical mu) := by
  intro a b k f hf
  have : translatesSpanCanonical mu ≤ (translatesSpanCanonical mu).comap (rowDivL ℚ a b k) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, rowDivL_apply]
    apply qd_vander
    intro t
    rw [qd_eval_rowGen, ← AlgHom.comp_apply, rowActMul]
    apply Submodule.subset_span
    exact ⟨_, by rw [Matrix.det_mul]; exact hg.mul (qd_det_E a b t), rfl⟩
  exact this hf

lemma qd_W_eq (mu : Fin n → ℤ) : translatesSpanCanonical mu = dualWeyl ℚ n n (qd_nu mu) := by
  have hcan : qd_P mu (canT mu) ∈ translatesSpanCanonical mu := by
    apply Submodule.subset_span
    exact ⟨1, by simp, by rw [ldrow_rowAct_one]; rfl⟩
  apply closedEqNabla n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ _ (qd_W_closed mu)
  · obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
    have : hw ℚ le_rfl (qd_nu mu) = c0⁻¹ • qd_P mu (canT mu) := by
      rw [h0, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hcan
  · unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, _, rfl⟩
    exact dualWeylRowStable ℚ n n _ g _ (tableauBideterminant_mem_dualWeyl' mu _)

omit [NeZero n] in
lemma qd_evGL_map {R' : Type} [CommRing R'] [Algebra ℚ R'] (γ : GL (Fin n) ℚ) (z : GLCoord ℤ n) :
    evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) z = algebraMap ℚ R' (evGL γ z) := by
  have h : evGL (Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) = (algebraMap ℚ R').comp (evGL γ) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h

omit [NeZero n] in
lemma qd_aeval_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1) P
      = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) (rowAct ℚ γ.val.transpose P) := by
  have h : aeval (R := ℚ) (fun v : Fin n × Fin n => (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ).val v.2 v.1)
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).comp (rowAct ℚ γ.val.transpose) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowAct, aeval_X, aeval_X, map_sum, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_X, aeval_C, Matrix.transpose_apply, mul_comm]
    rfl
  exact congrArg (fun φ => φ P) h

omit [NeZero n] in
lemma qd_ev_algebraMap {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (c : ℚ) :
    evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) c) = algebraMap ℚ R' c := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n), evGLR,
    IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

lemma qd_ev_L_mul {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ) (mu : Fin n → ℤ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_L mu P)
      = evGLR (R := ℚ) x (qd_L mu
        (((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose P)) := by
  rw [map_smul, qd_L_apply, qd_L_apply, map_mul, qd_ev_sig, qd_aeval_mul, Algebra.smul_def, map_mul, map_mul,
    qd_ev_sig]
  have h1 : evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_U mu)
      = evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        * evGLR (R := ℚ) x (qd_U mu) := by
    have h2 : evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        = algebraMap ℚ R' ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) :=
      qd_ev_algebraMap x _
    rw [h2, ← qd_evGL_detU, ← qd_evGL_map]
    unfold qd_U
    rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, qd_evGL_detU, map_mul, mul_zpow,
      Units.val_mul, mul_comm]
  rw [h1]
  ring

lemma qd_L_inj (mu : Fin n → ℤ) (P Q : MvPolynomial (Fin n × Fin n) ℚ)
    (h : evGLR (R := ℚ) (qd_genPt n) (qd_L mu P) = evGLR (R := ℚ) (qd_genPt n) (qd_L mu Q)) : P = Q := by
  rw [qd_L_apply, qd_L_apply, map_mul, map_mul] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, aeval_generic_point] at h2
  exact qd_sig_inj n (Polynomial.C_injective h2)

def qd_Lam (mu : Fin n → ℤ) : (TIdx mu → ℚ) →ₗ[ℚ] GLCoord ℚ n :=
  Fintype.linearCombination ℚ (fun K : TIdx mu => mapCoord ℚ (brk mu K))

lemma qd_Lam_apply (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    qd_Lam mu w = ∑ K, w K • mapCoord ℚ (brk mu K) := by
  rw [qd_Lam, Fintype.linearCombination_apply]

lemma qd_Lam_L (mu : Fin n → ℤ) (w : TIdx mu → ℚ) : qd_Lam mu w = qd_L mu (∑ K, w K • qd_P mu K) := by
  rw [qd_Lam_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P]

def qd_gcan (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) : TIdx mu → ℚ := fun K => evGL γ (TMat mu K (canT mu))

lemma qd_translate (mu : Fin n → ℤ) (γ : GL (Fin n) ℚ) :
    ∑ K, qd_gcan mu γ K • qd_P mu K =
      ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose (qd_P mu (canT mu)) := by
  apply qd_L_inj mu
  rw [← qd_ev_L_mul, qd_L_P, qd_evGLR_mapCoord, brk, qc_TMat_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_smul, qd_L_P, Algebra.smul_def, map_mul, qd_evGLR_mapCoord, qd_evGL_map, mul_comm]
  rw [qd_ev_algebraMap]
  rfl

theorem qd_gen (mu : Fin n → ℤ) (w : TIdx mu → ℚ) :
    ∃ w' ∈ Submodule.span ℚ (Set.range (qd_gcan mu)), qd_Lam mu w = qd_Lam mu w' := by
  have h1 : (∑ K, w K • qd_P mu K) ∈ translatesSpanCanonical mu := by
    rw [qd_W_eq]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl' mu K)
  have h2 : translatesSpanCanonical mu ≤ (Submodule.span ℚ (Set.range (qd_gcan mu))).map
      (Fintype.linearCombination ℚ (fun K : TIdx mu => qd_P mu K)) := by
    unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    set γ : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mk'' g.transpose (by rwa [Matrix.det_transpose]) with hγ
    have hv : γ.val.transpose = g := by
      rw [hγ]; exact Matrix.transpose_transpose g
    refine ⟨(((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))⁻¹ • qd_gcan mu γ,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, rfl⟩), ?_⟩
    rw [map_smul, Fintype.linearCombination_apply, qd_translate, hv, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨w', hw', he⟩ := h2 h1
  refine ⟨w', hw', ?_⟩
  rw [qd_Lam_L, qd_Lam_L, ← he, Fintype.linearCombination_apply]

end Formalism.InvariantFactorPaths.ColumnFamilies
