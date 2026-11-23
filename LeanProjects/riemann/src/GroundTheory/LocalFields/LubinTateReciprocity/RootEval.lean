import Mathlib

noncomputable section

namespace GroundTheory.LocalField

open PowerSeries

section HomExt

variable {B S : Type*} [CommRing B] [CommRing S]

theorem powerSeries_ringHom_ext {J : Ideal S} (hJ : ∀ z : S, (∀ k : ℕ, z ∈ J ^ k) → z = 0)
    {Φ₁ Φ₂ : B⟦X⟧ →+* S} (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ J) : Φ₁ = Φ₂ := by
  have hpoly : Φ₁.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) =
      Φ₂.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) := by
    apply Polynomial.ringHom_ext
    · intro b
      simpa using hC b
    · simpa using hX
  have hp : ∀ p : Polynomial B, Φ₁ (p : B⟦X⟧) = Φ₂ (p : B⟦X⟧) := fun p =>
    congrArg (fun Φ : Polynomial B →+* S => Φ p) hpoly
  ext F
  refine sub_eq_zero.mp (hJ _ fun k => ?_)
  set G : B⟦X⟧ := PowerSeries.mk fun i => coeff (i + k) F
  have hF : Φ₁ F - Φ₂ F = Φ₁ X ^ k * (Φ₁ G - Φ₂ G) := by
    conv_lhs => rw [F.eq_X_pow_mul_shift_add_trunc k]
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, hp, ← hX]
    ring
  rw [hF]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXJ k)

end HomExt

section RootEval

variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}

variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)

def rootEval : B⟦X⟧ →ₐ[B] AdjoinRoot P :=
  (hP.algEquivQuotient.symm.toAlgHom : B⟦X⟧ ⧸ Ideal.span {(P : B⟦X⟧)} →ₐ[B] AdjoinRoot P).comp
    (Ideal.Quotient.mkₐ B _)

theorem rootEval_coe (p : Polynomial B) : rootEval hP (p : B⟦X⟧) = AdjoinRoot.mk P p := by
  apply hP.algEquivQuotient.injective
  change hP.algEquivQuotient (hP.algEquivQuotient.symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

@[simp]
theorem rootEval_X : rootEval hP X = AdjoinRoot.root P := by
  rw [← Polynomial.coe_X, rootEval_coe]
  rfl

@[simp]
theorem rootEval_C (b : B) : rootEval hP (C b) = AdjoinRoot.of P b := by
  rw [← Polynomial.coe_C, rootEval_coe, AdjoinRoot.mk_C]

theorem rootEval_eq_zero_iff (F : B⟦X⟧) :
    rootEval hP F = 0 ↔ F ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change hP.algEquivQuotient.symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ hP.algEquivQuotient.symm.injective]
  rfl

theorem rootEval_eq_rootEval_iff (F G : B⟦X⟧) :
    rootEval hP F = rootEval hP G ↔ F - G ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← rootEval_eq_zero_iff hP, map_sub, sub_eq_zero]

theorem rootEval_self : rootEval hP (P : B⟦X⟧) = 0 := by
  rw [rootEval_coe, AdjoinRoot.mk_self]

theorem rootEval_subst_coe {G : B⟦X⟧} (hG : constantCoeff G = 0) (p : Polynomial B) :
    rootEval hP (subst G (p : B⟦X⟧)) = Polynomial.aeval (rootEval hP G) p := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' hG), Polynomial.aeval_algHom_apply]

theorem rootEval_mem_span_root {G : B⟦X⟧} (hG : constantCoeff G = 0) :
    rootEval hP G ∈ Ideal.span {AdjoinRoot.root P} := by
  obtain ⟨H, rfl⟩ := PowerSeries.X_dvd_iff.mpr hG
  rw [map_mul, rootEval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem isUnit_rootEval {G : B⟦X⟧} (hG : IsUnit (constantCoeff G)) :
    IsUnit (rootEval hP G) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hG).map _

end RootEval

section Hausdorff

variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}

theorem root_pow_mem_map (hP : P.IsDistinguishedAt I) :
    AdjoinRoot.root P ^ P.natDegree ∈ I.map (AdjoinRoot.of P) := by
  have h : Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)
      (Polynomial.X ^ P.natDegree +
        ∑ i ∈ Finset.range P.natDegree, Polynomial.C (P.coeff i) * Polynomial.X ^ i) = 0 := by
    rw [← hP.monic.as_sum]
    exact AdjoinRoot.eval₂_root P
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
  rw [eq_neg_of_add_eq_zero_left h, neg_mem_iff]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  exact Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (hP.mem (Finset.mem_range.mp hi)))

theorem repr_mem_of_mem_map (hP : P.Monic) (J : Ideal B) {z : AdjoinRoot P}
    (hz : z ∈ J.map (AdjoinRoot.of P)) (i : Fin (AdjoinRoot.powerBasis' hP).dim) :
    (AdjoinRoot.powerBasis' hP).basis.repr z i ∈ J := by
  have hz' : z ∈ J • (⊤ : Submodule B (AdjoinRoot P)) := by
    rw [Ideal.smul_top_eq_map]
    exact hz
  refine Submodule.smul_induction_on hz' (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact J.add_mem hx hy

theorem eq_zero_of_forall_mem_span_root_pow [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {z : AdjoinRoot P} (hz : ∀ k : ℕ, z ∈ Ideal.span {AdjoinRoot.root P} ^ k) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP.monic
  have hmem : ∀ k : ℕ, z ∈ (I ^ k).map (AdjoinRoot.of P) := by
    intro k
    have h := hz (P.natDegree * k)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨w, hw⟩ := h
    rw [hw, pow_mul, Ideal.map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (root_pow_mem_map hP) k)
  apply pb.basis.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus' (I := I) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact repr_mem_of_mem_map hP.monic _ (hmem k) i

theorem rootEval_ringHom_ext [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {Φ₁ Φ₂ : B⟦X⟧ →+* AdjoinRoot P}
    (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ Ideal.span {AdjoinRoot.root P}) : Φ₁ = Φ₂ :=
  powerSeries_ringHom_ext (fun _ hz => eq_zero_of_forall_mem_span_root_pow hP hz) hC hX hXJ

end Hausdorff

section Coordinates

variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem eq_zero_of_of_mul_eq_zero (hP : P.Monic) {b : B} (hb : ∀ c : B, b * c = 0 → c = 0)
    {z : AdjoinRoot P} (h : AdjoinRoot.of P b * z = 0) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP
  have h' : b • z = 0 := by
    rw [Algebra.smul_def]
    exact h
  apply pb.basis.repr.injective
  ext i
  have := congrArg (fun w => pb.basis.repr w i) h'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  rw [map_zero, Finsupp.zero_apply]
  exact hb _ this

theorem eq_zero_of_mul_eq_zero_of_pow_eq (hP : P.Monic) {b : B}
    (hb : ∀ c : B, b * c = 0 → c = 0) {y : AdjoinRoot P} {k : ℕ} (hk : k ≠ 0)
    (hy : y ^ k = AdjoinRoot.of P b) {z : AdjoinRoot P} (h : y * z = 0) : z = 0 := by
  refine eq_zero_of_of_mul_eq_zero hP hb ?_
  rw [← hy]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ, mul_assoc, h, mul_zero]

end Coordinates

end GroundTheory.LocalField
