import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliMain

noncomputable section

namespace PI.HookSteps.Cap

open MvPolynomial Finset

theorem mulLeft_eq_lmul (N : ℕ) (p : MvPolynomial (Fin N × Fin N) ℚ) :
    LinearMap.mulLeft ℚ p = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) p := rfl

theorem capelli_relation : CapRel := by
  intro N
  refine ⟨fun a s b t => ?_, fun a s b t => ?_⟩
  · refine LinearMap.ext fun p => ?_
    have e1 : (xo N a s * xo N b t) p = X (a, s) * (X (b, t) * p) := rfl
    have e2 : (xo N b t * xo N a s) p = X (b, t) * (X (a, s) * p) := rfl
    rw [e1, e2]
    exact mul_left_comm _ _ _
  · refine LinearMap.ext fun p => ?_
    have e1 : (dop N b t * xo N a s) p = pderiv (b, t) (X (a, s) * p) := rfl
    have e2 : (xo N a s * dop N b t) p = X (a, s) * pderiv (b, t) p := rfl
    rw [LinearMap.add_apply, e1, e2, Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Pi.single_apply, if_neg (fun e => h (Prod.mk.inj e))]
      simp

theorem capelli_left_holds : CapLeft := by
  intro N
  unfold Formalism.CohomologicalDescent.HeightDescentMinors.capelli Lw
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  funext j
  have hE : polE N (σ j) j = Eop (xo N) (dop N) (σ j) (id j) := rfl
  simp only [Formalism.CohomologicalDescent.HeightDescentMinors.capA, hE, id]
  congr 2
  simp [map_sub, map_natCast]

theorem dop_comm (N : ℕ) (b t b' t' : Fin N) : Commute (dop N b t) (dop N b' t') := by
  have h : ⁅(pderiv (b, t) : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ)),
      (pderiv (b', t') : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  apply LinearMap.ext; intro f
  have := congrArg (fun D : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ)
    (MvPolynomial (Fin N × Fin N) ℚ) => D f) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  simpa [dop, Module.End.mul_apply, sub_eq_zero] using this

theorem xw_xo (N : ℕ) : ∀ (k : ℕ) (r s : Fin k → Fin N),
    xw (xo N) r s = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) (∏ j, X (r j, s j)) := by
  intro k
  induction k with
  | zero =>
    intro r s
    rw [xw_zero]
    refine LinearMap.ext fun p => ?_
    simp
  | succ k ih =>
    intro r s
    rw [xw_succ, ih, Fin.prod_univ_succ, map_mul]
    rfl

theorem sum_perm_of_noninj {M : Type} [AddCommMonoid M] (N : ℕ) (F : (Fin N → Fin N) → M)
    (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ π : Equiv.Perm (Fin N), F π := by
  classical
  have himg : ∑ π : Equiv.Perm (Fin N), F π =
      ∑ s ∈ Finset.univ.image (fun π : Equiv.Perm (Fin N) => (π : Fin N → Fin N)), F s :=
    (Finset.sum_image fun π _ σ _ h => Equiv.ext (congrFun h)).symm
  rw [himg]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_
  exact Finset.mem_image.2
    ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩

theorem detD_eq (N : ℕ) : detD N = ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤˣ) : ℤ) •
    dw (dop N) (id : Fin N → Fin N) (fun j => π j) := by
  unfold detD
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  unfold dw
  have hp := Equiv.Perm.ofFn_comp_perm σ⁻¹ (fun j => dop N j (σ j))
  have hc : (List.ofFn ((fun j => dop N j (σ j)) ∘ ⇑σ⁻¹)).Pairwise Commute :=
    List.pairwise_ofFn.mpr fun i j _ => dop_comm N _ _ _ _
  refine Eq.trans ?_ ((hp.prod_eq' hc).trans rfl)
  congr 1
  congr 1
  funext j
  simp [dop]

theorem capelli_square : CapSquare := by
  intro N
  set P := MvPolynomial (Fin N × Fin N) ℚ
  set M : Matrix (Fin N) (Fin N) P := Matrix.of fun a b => (X (a, b) : P) with hM
  have hdet : ∀ s : Fin N → Fin N, ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      xw (xo N) (fun j => σ j) s = Algebra.lmul ℚ P (M.submatrix id s).det := by
    intro s
    rw [Matrix.det_apply, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [xw_xo, Units.smul_def, map_zsmul]
    rfl
  unfold Pn
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, hdet]
  rw [sum_perm_of_noninj N (fun s => Algebra.lmul ℚ P (M.submatrix id s).det * dw (dop N) id s)]
  · rw [detD_eq, Finset.mul_sum, mulLeft_eq_lmul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Matrix.det_permute', map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]
    rfl
  · intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij]), map_zero, zero_mul]

theorem capelli_determinant_identity : PI.HookSteps.DetDetId :=
  detDetId_of capelli_absolute_value capelli_square capelli_left_holds capelli_relation

end PI.HookSteps.Cap
