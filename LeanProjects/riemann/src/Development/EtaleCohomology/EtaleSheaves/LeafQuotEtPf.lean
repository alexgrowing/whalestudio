import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPPf

noncomputable section
open TensorProduct

namespace LateralTheory.E.LeafQuotEtPf

abbrev J0 (d : ℕ) (C : Type) [CommRing C] : Ideal (MvPolynomial (Fin d) C) :=
  Ideal.span (Set.range fun j => MvPolynomial.X j)

theorem sub_C_mem {d : ℕ} {C : Type} [CommRing C] (p : MvPolynomial (Fin d) C) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ J0 d C := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have : p + q - MvPolynomial.C (MvPolynomial.constantCoeff (p + q)) =
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) +
        (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by simp; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p i _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem ideal_zero_le_ker_constant_coeff {d : ℕ} {C : Type} [CommRing C] :
    J0 d C ≤ RingHom.ker (MvPolynomial.constantCoeff (R := C) (σ := Fin d)) := by
  rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩; simp

theorem bij (d : ℕ) (C : Type) [CommRing C] :
    Function.Bijective ((Ideal.Quotient.mk (J0 d C)).comp MvPolynomial.C) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h := ideal_zero_le_ker_constant_coeff (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    simpa using h
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq]
    have := (J0 d C).neg_mem (sub_C_mem p)
    simpa using this

theorem LeafQuotEt_of : LateralTheory.E.LeafRoofEtPPf.LeafQuotEt := by
  intro d C B _ _ φ hφ
  let A := MvPolynomial (Fin d) C
  let _ : Algebra A B := φ.toAlgebra
  have : Algebra.Etale A B := RingHom.etale_algebraMap.mp hφ
  have hI : (J0 d C).map (algebraMap A B) = LateralTheory.E.t_E6Cut.varIdeal φ := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  let e0 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (J0 d C)
  let e : (A ⧸ J0 d C) ⊗[A] B ≃+* B ⧸ LateralTheory.E.t_E6Cut.varIdeal φ :=
    ((Algebra.TensorProduct.comm A (A ⧸ J0 d C) B).toRingEquiv.trans e0.symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hI)
  have hg : (algebraMap (A ⧸ J0 d C) ((A ⧸ J0 d C) ⊗[A] B)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.baseChange A B (A ⧸ J0 d C))
  have h1 : (e.toRingHom.comp (algebraMap (A ⧸ J0 d C) ((A ⧸ J0 d C) ⊗[A] B))).Etale :=
    RingHom.Etale.respectsIso.1 _ e hg
  have h2 := RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (bij d C)) h1
  convert h2 using 1
  ext c
  simp only [RingHom.comp_apply]
  show _ = e (Ideal.Quotient.mk (J0 d C) (MvPolynomial.C c) ⊗ₜ[A] (1 : B))
  have : (Ideal.Quotient.mk (J0 d C) (MvPolynomial.C c) ⊗ₜ[A] (1 : B)) =
      (1 : A ⧸ J0 d C) ⊗ₜ[A] φ (MvPolynomial.C c) := by
    have h3 : Ideal.Quotient.mk (J0 d C) (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : A ⧸ J0 d C) := by
      rw [Algebra.smul_def, mul_one]; rfl
    have h4 : φ (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : B) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [h3, h4, TensorProduct.smul_tmul]
  rw [this]
  show _ = Ideal.quotEquivOfEq hI (e0.symm (φ (MvPolynomial.C c) ⊗ₜ[A] (1 : A ⧸ J0 d C)))
  have h5 : e0.symm (φ (MvPolynomial.C c) ⊗ₜ[A] (1 : A ⧸ J0 d C)) = Ideal.Quotient.mk _ (φ (MvPolynomial.C c)) := by
    rw [AlgEquiv.symm_apply_eq]
    simp [e0]
    rfl
  rw [h5]
  rfl

end LateralTheory.E.LeafQuotEtPf
