import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonEigenvectorCommuting
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ContraChar

open ReciprocityTheory.ChartRestriction.TR.Weyl

theorem map_gtChar (σ : ℂ →+* ℂ) : ∀ (n : ℕ) (l : Fin n → ℤ) (t : Fin n → ℂ),
    σ (gtChar n l t) = gtChar n l (fun i => σ (t i))
  | 0, l, t => by simp [gtChar]
  | n + 1, l, t => by
    simp only [gtChar, map_sum, map_mul, map_zpow₀]
    refine Finset.sum_congr rfl fun mu _ => ?_
    rw [map_gtChar σ n mu]

theorem trace_sqRep_diag {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) ℂ) (t : Fin n → ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = diagonal t) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) = gtChar n lam.w t := by
  obtain ⟨f, hf, htr⟩ := sqChar n lam g t hg
  have e : f = GlobalTheory.Branching.sqRep ℂ n lam g :=
    LinearMap.ext fun x => Subtype.ext (by rw [hf, GlobalTheory.Branching.sqRep_coe])
  rw [← e, htr]

theorem trace_sqRep_conj {n : ℕ} (lam : DomWeight n) (P g : GL (Fin n) ℂ) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (P * g * P⁻¹)) =
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) := by
  have e2 : GlobalTheory.Branching.sqRep ℂ n lam P⁻¹ * GlobalTheory.Branching.sqRep ℂ n lam P = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul (GlobalTheory.Branching.sqRep ℂ n lam), map_mul (GlobalTheory.Branching.sqRep ℂ n lam), mul_assoc,
    LinearMap.trace_mul_comm, mul_assoc, e2, mul_one]

theorem exists_poly_trace {n : ℕ} (lam : DomWeight n) :
    ∃ Q : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) =
        detPow ℂ n g lam.detShift * MvPolynomial.eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.2 x.1) Q := by
  let B := Module.finBasis ℂ (nablaSq ℂ n lam)
  have hL : ∀ i, ∃ L : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      L ∘ₗ (nablaSq ℂ n lam).subtype = B.coord i := fun i => LinearMap.exists_extend (B.coord i)
  choose L hL using hL
  have hP : ∀ i, ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ A : Matrix (Fin n) (Fin n) ℂ,
      L i (Formalism.GradedWeylDivisibility.rowAct ℂ A (B i : MvPolynomial (Fin n × Fin n) ℂ)) =
        MvPolynomial.eval (fun x => A x.1 x.2) P :=
    fun i => GlobalTheory.Branching.exists_poly_rowAct_coef n n _ (L i)
  choose P hP using hP
  refine ⟨∑ i, P i, fun g => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have h1 := LinearMap.congr_fun (hL i) (GlobalTheory.Branching.sqRep ℂ n lam g (B i))
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at h1
  rw [← h1, GlobalTheory.Branching.sqRep_coe, sqAct, map_smul, hP, smul_eq_mul]
  rfl

theorem detPow_conj {n : ℕ} (P g : GL (Fin n) ℂ) (c : ℤ) :
    detPow ℂ n (P * g * P⁻¹) c = detPow ℂ n g c := by
  unfold detPow
  rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det P), mul_inv_cancel_right]

theorem trace_sqRep_of_upper {n : ℕ} (lam : DomWeight n) (T D : GL (Fin n) ℂ)
    (hT : (T : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id)
    (hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (T : Matrix (Fin n) (Fin n) ℂ) i i) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam T) =
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam D) := by
  obtain ⟨Q, hQ⟩ := exists_poly_trace lam
  set A : Matrix (Fin n) (Fin n) ℂ := (T : Matrix (Fin n) (Fin n) ℂ) with hA
  let φ : ℂ → ℂ := fun u => MvPolynomial.eval (fun x : Fin n × Fin n => A x.2 x.1 * u ^ ((x.1 : ℕ) - (x.2 : ℕ))) Q
  have hdetT : detPow ℂ n D lam.detShift = detPow ℂ n T lam.detShift := by
    unfold detPow
    congr 2
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hD, det_diagonal,
      ← hA, Matrix.det_of_isUpperTriangular hT]
  have hne : detPow ℂ n T lam.detShift ≠ 0 := Units.ne_zero _
  have hconj : ∀ u : ℂ, u ≠ 0 →
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam T) = detPow ℂ n T lam.detShift * φ u := by
    intro u hu
    let U : ℂˣ := Units.mk0 u hu
    let Du : GL (Fin n) ℂ := diagGL ℂ n fun i : Fin n => U⁻¹ ^ (i : ℕ)
    have hM : ∀ i j, ((Du * T * Du⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j =
        A i j * u ^ ((j : ℕ) - (i : ℕ)) := by
      intro i j
      change (diagonal (fun a : Fin n => ((U⁻¹ ^ (a : ℕ) : ℂˣ) : ℂ)) * A *
        diagonal (fun a : Fin n => (((U⁻¹ ^ (a : ℕ))⁻¹ : ℂˣ) : ℂ))) i j = _
      rw [mul_diagonal, diagonal_mul]
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, U, inv_pow, inv_inv]
      by_cases hji : j < i
      · rw [hT hji]; ring
      · have hij : (i : ℕ) ≤ j := by rw [not_lt, Fin.le_iff_val_le_val] at hji; exact hji
        have e : u ^ (j : ℕ) = u ^ (i : ℕ) * u ^ ((j : ℕ) - (i : ℕ)) := by
          rw [← pow_add, Nat.add_sub_cancel' hij]
        rw [e]
        field_simp
    rw [← trace_sqRep_conj lam Du T, hQ, detPow_conj]
    congr 1
    exact congrArg (fun f => MvPolynomial.eval f Q) (funext fun x => hM x.2 x.1)
  have hφc : Continuous φ :=
    (MvPolynomial.continuous_eval Q).comp (continuous_pi fun x => continuous_const.mul (continuous_pow _))
  have hφ : φ = fun _ => φ 1 := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hφc continuous_const fun u hu => ?_
    have h1 := hconj u hu
    rw [hconj 1 one_ne_zero] at h1
    exact (mul_left_cancel₀ hne h1).symm
  have h0 : φ 0 = MvPolynomial.eval (fun x => (D : Matrix (Fin n) (Fin n) ℂ) x.2 x.1) Q := by
    refine congrArg (fun f => MvPolynomial.eval f Q) (funext fun x => ?_)
    rw [hD, diagonal_apply]
    by_cases h : x.2 = x.1
    · rw [if_pos h, h, Nat.sub_self, pow_zero, mul_one]
    · rw [if_neg h]
      rcases lt_or_gt_of_ne h with h' | h'
      · rw [zero_pow (by rw [Fin.lt_def] at h'; omega), mul_zero]
      · rw [hT h', zero_mul]
  rw [hQ D, hdetT, ← h0, congrFun hφ 0, hconj 1 one_ne_zero]

theorem exists_eig {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) ℂ) :
    ∃ d : Fin n → ℂ, (∀ i, d i ≠ 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (X - C (d i)) ∧
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) = gtChar n lam.w d := by
  obtain ⟨P, hP, hT, -⟩ :=
    GlobalTheory.CommTriang.exists_triangular ℂ Unit n (fun _ => (g : Matrix (Fin n) (Fin n) ℂ)) (fun _ _ => rfl)
  let Pu : GL (Fin n) ℂ := hP.unit
  let T : GL (Fin n) ℂ := Pu⁻¹ * g * Pu
  have hTv : (T : Matrix (Fin n) (Fin n) ℂ) = P⁻¹ * g * P := by
    simp only [T, Units.val_mul, Matrix.coe_units_inv, Pu, IsUnit.unit_spec]
  have hTt : (T : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := by rw [hTv]; exact hT ()
  have hdet : ∀ i, (T : Matrix (Fin n) (Fin n) ℂ) i i ≠ 0 := by
    intro i h
    have hd : (T : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_of_isUpperTriangular hTt] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let D : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hdet i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (T : Matrix (Fin n) (Fin n) ℂ) i i := by
    change diagonal (fun a => ((Units.mk0 _ (hdet a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  refine ⟨fun i => (T : Matrix (Fin n) (Fin n) ℂ) i i, hdet, ?_, ?_⟩
  · have h := Matrix.charpoly_units_conj (Pu⁻¹) (g : Matrix (Fin n) (Fin n) ℂ)
    rw [← Matrix.coe_units_inv, inv_inv, ← Units.val_mul, ← Units.val_mul] at h
    rw [← h]
    exact Matrix.charpoly_of_isUpperTriangular _ hTt
  · have hg : g = Pu * T * Pu⁻¹ := by simp only [T, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rw [hg, trace_sqRep_conj, trace_sqRep_of_upper lam T D hTt hD, trace_sqRep_diag lam D _ hD]

theorem exists_perm_of_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

def permGL {n : ℕ} (π : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

theorem gtChar_perm {n : ℕ} (lam : DomWeight n) (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) (π : Equiv.Perm (Fin n)) :
    gtChar n lam.w (fun i => d (π i)) = gtChar n lam.w d := by
  let D : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hd i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
    change diagonal (fun a => ((Units.mk0 _ (hd a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hDπ : ((permGL π * D * (permGL π)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      diagonal fun i => d (π i) := by
    rw [Units.val_mul, Units.val_mul, hD]
    change π.toPEquiv.toMatrix * diagonal d * π.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    exact submatrix_diagonal_equiv d π
  rw [← trace_sqRep_diag lam D d hD, ← trace_sqRep_diag lam _ _ hDπ, trace_sqRep_conj]

theorem trace_sqRep_eq_of_charpoly_eq {n : ℕ} (lam : DomWeight n) (g h : GL (Fin n) ℂ)
    (hc : (g : Matrix (Fin n) (Fin n) ℂ).charpoly = (h : Matrix (Fin n) (Fin n) ℂ).charpoly) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) = LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam h) := by
  obtain ⟨d, hd0, hdc, hdt⟩ := exists_eig lam g
  obtain ⟨d', -, hdc', hdt'⟩ := exists_eig lam h
  have hr : ∀ e : Fin n → ℂ, (∏ i, (X - C (e i))).roots = Finset.univ.val.map e := fun e => by
    rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map e), Multiset.map_map]
    rfl
  have hm : Finset.univ.val.map d = Finset.univ.val.map d' := by rw [← hr, ← hr, ← hdc, ← hdc', hc]
  obtain ⟨π, hπ⟩ := exists_perm_of_map_eq d d' hm
  rw [hdt, hdt', ← funext hπ, gtChar_perm lam d hd0 π]

theorem trace_sqRep_inv_eq_conj_chAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : DomWeight n) (γ : UE E n) (v : InfinitePlace E),
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map v.embedding (γ⁻¹).1)) =
      starRingEnd ℂ (chAt lam (γ.1.val.charpoly.map v.embedding)) := by
  intro E _ _ _ n lam γ v
  set τ : E →+* ℂ := v.embedding with hτ
  set g : GL (Fin n) ℂ := GeneralLinearGroup.map τ γ.1 with hg
  have hinv : GeneralLinearGroup.map τ (γ⁻¹).1 = g⁻¹ := by rw [Subgroup.coe_inv, map_inv]
  have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = (γ.1 : Matrix (Fin n) (Fin n) E).map τ := rfl
  have hcp : γ.1.val.charpoly.map τ = (g : Matrix (Fin n) (Fin n) ℂ).charpoly := by rw [hgv, charpoly_map]
  have hu : ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (g : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    rw [Matrix.mul_one] at h
    have h2 := congrArg (fun M => M.map τ) h
    simp only [Matrix.map_mul, Matrix.map_one τ (map_zero τ) (map_one τ)] at h2
    rw [← h2, hgv]
    congr 1
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
    exact (IsCMField.complexEmbedding_complexConj E τ _).symm
  have hginv : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hu
  obtain ⟨d, hd0, hdc, -⟩ := exists_eig lam g
  have hcd : ∀ i, starRingEnd ℂ (d i) ≠ 0 := fun i => by simpa using hd0 i
  let Dc : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hcd i)
  let D : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hd0 i)
  have hDc : (Dc : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => starRingEnd ℂ (d i) := by
    change diagonal (fun a => ((Units.mk0 _ (hcd a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
    change diagonal (fun a => ((Units.mk0 _ (hd0 a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have cpD : (D : Matrix (Fin n) (Fin n) ℂ).charpoly = (g : Matrix (Fin n) (Fin n) ℂ).charpoly := by
    rw [hD, charpoly_diagonal, hdc]
  have cpDc : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (Dc : Matrix (Fin n) (Fin n) ℂ).charpoly := by
    rw [hginv, charpoly_transpose, charpoly_map, hdc, hDc, charpoly_diagonal, Polynomial.map_prod]
    simp
  rw [hinv, hcp, trace_sqRep_eq_of_charpoly_eq lam _ Dc cpDc, trace_sqRep_diag lam Dc _ hDc]
  have hex : ∃ h : GL (Fin n) ℂ, (h : Matrix (Fin n) (Fin n) ℂ).charpoly = (g : Matrix (Fin n) (Fin n) ℂ).charpoly :=
    ⟨g, rfl⟩
  unfold chAt
  rw [dif_pos hex, trace_sqRep_eq_of_charpoly_eq lam _ D (hex.choose_spec.trans cpD.symm),
    trace_sqRep_diag lam D _ hD, map_gtChar]

end GlobalTheory.ContraChar
