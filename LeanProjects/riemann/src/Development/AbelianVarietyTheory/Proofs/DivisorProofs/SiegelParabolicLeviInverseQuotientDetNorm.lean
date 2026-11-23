import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagLevi

theorem det_sub_one_ann {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (e : R)
    (M : Matrix ι ι R) (h : ∀ i j, e * (M i j - (1 : Matrix ι ι R) i j) = 0) : e * (M.det - 1) = 0 := by
  set I : Ideal R := (Submodule.span R {e}).annihilator
  have hI : ∀ a, a ∈ I ↔ a * e = 0 := fun a => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    ext i j
    rw [← map_one (Ideal.Quotient.mk I).mapMatrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, hI, mul_comm]
    exact h i j
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, Matrix.det_one, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hI] at h2
  rw [mul_comm]; exact h2

end GlobalTheory.InertLagLevi

open GlobalTheory.InertLagLevi in
theorem GlobalTheory.InertLagLevi.levi_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl F) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (AE F E), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  intro F E _ _ _ _ _ σ hσ n J hJ v p t hsupp hpt
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := p.1.1 with hP
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := (p⁻¹).1.1 with hQ
  set D : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hD
  set T := t.val with hT
  set Ti := (t⁻¹).val with hTi
  have hTTi : T * Ti = 1 := by simp [T, Ti]
  have hQP : Q * P = 1 := by simp [Q, P]

  have htsupp : ∀ u : AF F, evFin F v u = 0 → u • (T - 1) = 0 := by
    intro u hu
    have h0 : u • (P - 1) = 0 := hsupp u hu
    have h1 : u • (P * D - D) = 0 := by
      rw [show P * D - D = (P - 1) * D by rw [Matrix.sub_mul, Matrix.one_mul], ← Matrix.smul_mul, h0, Matrix.zero_mul]
    rw [show P * D = D * T from hpt, show D * T - D = Matrix.fromRows (T - 1) (T - 1) by
      ext (i|i) j <;> simp [D, diagCols, Matrix.fromRows_mul]] at h1
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) j
    simpa using this
  have hdet : ∀ u : AF F, evFin F v u = 0 → u • (T.det - 1) = 0 := by
    intro u hu
    have h := htsupp u hu
    rw [Algebra.smul_def]
    refine det_sub_one_ann _ T fun i j => ?_
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply, Matrix.sub_apply, Algebra.smul_def] at this
  refine ⟨hdet, ?_, ?_⟩
  · intro u hu
    have hz := hdet u hu
    let b := Module.Free.chooseBasis (AF F) (AE F E)
    rw [Algebra.norm_eq_matrix_det b, smul_eq_mul]
    refine det_sub_one_ann _ _ fun i j => ?_
    rw [← Matrix.sub_apply, ← map_one (Algebra.leftMulMatrix b), ← map_sub, Algebra.leftMulMatrix_eq_repr_mul,
      ← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← smul_mul_assoc, hz, zero_mul, map_zero, Finsupp.zero_apply]
  · have hpt' : P * D = D * T := hpt
    set K : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows 1 (-1) with hKdef
    have hq : Qᵀ * dbl (incM F J) * Q.map (cA σ) = dbl (incM F J) := (p⁻¹).2
    have hQD : Q * D = D * Ti := by
      calc Q * D = Q * (D * T * Ti) := by rw [Matrix.mul_assoc D, hTTi, Matrix.mul_one]
        _ = Q * P * D * Ti := by
          rw [Matrix.mul_assoc Q P D, hpt']; simp only [Matrix.mul_assoc]
        _ = D * Ti := by rw [hQP, Matrix.one_mul]
    have hDc : D.map (cA σ) = D := by
      simp only [D, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    have hK : dbl (incM F J) * D = K * incM F J := by
      simp only [dbl, D, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
      simp [K, Matrix.fromRows_mul]
    have h2 : Qᵀ * (K * incM F J) * Ti.map (cA σ) = K * incM F J := by
      rw [← hK]
      calc Qᵀ * (dbl (incM F J) * D) * Ti.map (cA σ)
          = Qᵀ * dbl (incM F J) * (D.map (cA σ) * Ti.map (cA σ)) := by rw [hDc]; simp only [Matrix.mul_assoc]
        _ = Qᵀ * dbl (incM F J) * (Q.map (cA σ) * D.map (cA σ)) := by
          have hm1 : (Q * D).map (cA σ) = Q.map (cA σ) * D.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          have hm2 : (D * Ti).map (cA σ) = D.map (cA σ) * Ti.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          rw [← hm1, ← hm2, hQD]
        _ = dbl (incM F J) * D := by rw [hDc, ← Matrix.mul_assoc, hq]
    set X := Q.toBlocks₁₁ - Q.toBlocks₂₁ with hX
    have hQK : Qᵀ * K = Matrix.fromRows Xᵀ (Q.toBlocks₁₂ - Q.toBlocks₂₂)ᵀ := by
      rw [hKdef, ← Matrix.transpose_transpose (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1)),
        ← Matrix.transpose_mul, Matrix.transpose_fromRows]
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Q]
      rw [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
      simp [X, sub_eq_add_neg]
    rw [← Matrix.mul_assoc, hQK, hKdef, Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.fromRows_mul] at h2
    have h3 : Xᵀ * incM F J * Ti.map (cA σ) = incM F J := by
      have := (Matrix.fromRows_inj h2).1
      rw [this, Matrix.one_mul]
    have hdJ : (incM F J).det = inclR (AF F) J.det := (RingHom.map_det _ J).symm
    have hJu : IsUnit (incM F J).det := hdJ ▸ (Ne.isUnit hJ).map _
    have hdTi : (Ti.map (cA σ)).det = cA σ Ti.det := (AlgHom.map_det (cA σ) Ti).symm
    have hx : X.det * cA σ Ti.det = 1 := by
      have := congrArg Matrix.det h3
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdTi, mul_right_comm] at this
      exact (hJu.mul_left_inj).1 (this.trans (one_mul _).symm)
    have hTd : T.det * Ti.det = 1 := by rw [← Matrix.det_mul, hTTi, Matrix.det_one]
    have hXd : X.det = cA σ T.det := by
      calc X.det = X.det * (cA σ Ti.det * cA σ T.det) := by
            rw [← map_mul, mul_comm Ti.det, hTd, map_one, mul_one]
        _ = (X.det * cA σ Ti.det) * cA σ T.det := by ring
        _ = cA σ T.det := by rw [hx, one_mul]
    refine ⟨Matrix.nonsingInvUnit X (isUnit_iff_exists_inv.mpr ⟨_, hx⟩), rfl, ?_⟩
    show Algebra.norm (AF F) X.det = _
    have hcc : ∀ x, cA σ (cA σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [cA, GlobalTheory.AdelicU.cm_conj_conj hσ]
      | add x y hx hy => simp [hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    rw [hXd]
    exact Algebra.norm_eq_of_algEquiv cE T.det
