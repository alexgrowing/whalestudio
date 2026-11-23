import Mathlib

open Matrix IsLocalRing

namespace DVRLatticeIndex

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

noncomputable def scaleAt {ι : Type*} [DecidableEq ι] (j : ι) (a : O) : Matrix ι ι O :=
  Matrix.diagonal (Function.update (fun _ => (1 : O)) j a)

theorem det_scaleAt {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (a : O) :
    (scaleAt j a).det = a := by
  simp [scaleAt, Matrix.det_diagonal, Function.update_apply, Finset.prod_ite_eq']

theorem range_toLin'_eq_top_of_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι O) (h : IsUnit C.det) : LinearMap.range (Matrix.toLin' C) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  refine ⟨C⁻¹ *ᵥ y, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]

theorem card_quot_range_of_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι O) (h : IsUnit C.det) :
    Nat.card ((ι → O) ⧸ LinearMap.range (Matrix.toLin' C)) = 1 := by
  rw [range_toLin'_eq_top_of_isUnit_det C h]
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact (Submodule.Quotient.eq _).mpr Submodule.mem_top

theorem injective_toLin'_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι O) (h : C.det ≠ 0) : Function.Injective (Matrix.toLin' C) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [Matrix.toLin'_apply] at hx
  have h2 : C.adjugate *ᵥ (C *ᵥ x) = C.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hx, Matrix.mulVec_zero] at h2
  funext i
  have h3 := congrFun h2 i
  rw [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.mp h3.symm).resolve_left h

theorem card_quot_range_comp {M : Type*} [AddCommGroup M] [Module O M]
    (A B : M →ₗ[O] M) (hA : Function.Injective A) :
    Nat.card (M ⧸ LinearMap.range (A ∘ₗ B)) =
      Nat.card (M ⧸ LinearMap.range B) * Nat.card (M ⧸ LinearMap.range A) := by
  have h1 : (LinearMap.range (A ∘ₗ B)).toAddSubgroup =
      (LinearMap.range B).toAddSubgroup.map A.toAddMonoidHom := by
    rw [LinearMap.range_comp, Submodule.map_toAddSubgroup]
    rfl
  have h2 : A.toAddMonoidHom.range = (LinearMap.range A).toAddSubgroup := by
    ext y
    simp
  change (LinearMap.range (A ∘ₗ B)).toAddSubgroup.index =
    (LinearMap.range B).toAddSubgroup.index * (LinearMap.range A).toAddSubgroup.index
  rw [h1, AddSubgroup.index_map_of_injective _ hA, h2]

theorem card_quot_range_scaleAt {ι : Type*} [Fintype ι] [DecidableEq ι] (ϖ : O)
    (hϖ : Irreducible ϖ) (j : ι) :
    Nat.card ((ι → O) ⧸ LinearMap.range (Matrix.toLin' (scaleAt j ϖ))) =
      Nat.card (IsLocalRing.ResidueField O) := by
  classical
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hrange : LinearMap.range (Matrix.toLin' (scaleAt j ϖ)) =
      LinearMap.ker ((Algebra.linearMap O (IsLocalRing.ResidueField O)) ∘ₗ LinearMap.proj j) := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply,
      Algebra.linearMap_apply]
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hmax,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, rfl⟩
      rw [Matrix.toLin'_apply]
      simp [scaleAt, Matrix.mulVec_diagonal]
    · rintro ⟨c, hc⟩
      refine ⟨Function.update y j c, ?_⟩
      funext i
      rw [Matrix.toLin'_apply]
      simp only [scaleAt, Matrix.mulVec_diagonal, Function.update_apply]
      split_ifs with h
      · subst h
        exact hc.symm
      · simp
  rw [hrange]
  have hsurj : Function.Surjective ((Algebra.linearMap O (IsLocalRing.ResidueField O)) ∘ₗ
      (LinearMap.proj j : (ι → O) →ₗ[O] O)) := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨Pi.single j a, by simp [IsLocalRing.ResidueField.algebraMap_eq]⟩
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hsurj).toEquiv

theorem card_quot_range_toLin_clean {ι : Type*} [Fintype ι] [DecidableEq ι] (ϖ : O)
    (hϖ : Irreducible ϖ) (C : Matrix ι ι O) (e : ℕ) (w : Oˣ) (hC : C.det = ϖ ^ e * w) :
    Nat.card ((ι → O) ⧸ LinearMap.range (Matrix.toLin' C)) =
      Nat.card (IsLocalRing.ResidueField O) ^ e := by
  classical
  induction e generalizing C w with
  | zero =>
    rw [pow_zero, one_mul] at hC
    rw [pow_zero]
    exact card_quot_range_of_isUnit_det C (by rw [hC]; exact w.isUnit)
  | succ e ih =>
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
    have hres : IsLocalRing.residue O ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hdetb : (C.map (IsLocalRing.residue O)).det = 0 := by
      rw [show (C.map (IsLocalRing.residue O)).det = IsLocalRing.residue O C.det from (RingHom.map_det _ _).symm,
        hC, map_mul, map_pow, hres, zero_pow (Nat.succ_ne_zero e), zero_mul]
    obtain ⟨vb, hvb0, hCvb⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetb
    choose vlift hvlift using fun i => IsLocalRing.residue_surjective (vb i)
    obtain ⟨i0, hi0⟩ : ∃ i0, vb i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hvb0 (funext h)
    have hunit : IsUnit (vlift i0) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hvlift]
      exact hi0
    have hdiv : ∀ m, ϖ ∣ (C *ᵥ vlift) m := by
      intro m
      have h1 : IsLocalRing.residue O ((C *ᵥ vlift) m) = 0 := by
        have h3 := congrFun hCvb m
        rw [Pi.zero_apply] at h3
        rw [← h3]
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hvlift]
      rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at h1
      exact h1
    choose c hc using hdiv
    set P : Matrix ι ι O := (1 : Matrix ι ι O).updateCol i0 vlift with hP
    set C' : Matrix ι ι O := C.updateCol i0 c with hC'
    have hdetP : P.det = vlift i0 := by
      rw [hP, ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    have hCP : C * P = C' * scaleAt i0 ϖ := by
      refine Matrix.ext fun m b => ?_
      rw [scaleAt, Matrix.mul_diagonal, Matrix.mul_apply]
      by_cases hb : b = i0
      · subst hb
        simp only [hP, hC', Matrix.updateCol_self, Function.update_self]
        have h2 := hc m
        simp only [Matrix.mulVec, dotProduct] at h2
        rw [h2, mul_comm]
      · simp only [hP, hC', Matrix.updateCol_ne hb, Function.update_of_ne hb, mul_one]
        rw [← Matrix.mul_apply, Matrix.mul_one]
    have hdetC' : C'.det = ϖ ^ e * ((w * hunit.unit : Oˣ) : O) := by
      have h1 : C'.det * ϖ = ϖ ^ (e + 1) * w * vlift i0 := by
        have h2 : (C' * scaleAt i0 ϖ).det = C'.det * ϖ := by rw [Matrix.det_mul, det_scaleAt]
        rw [← h2, ← hCP, Matrix.det_mul, hC, hdetP]
      apply mul_right_cancel₀ hϖ0
      rw [h1]
      simp only [Units.val_mul, IsUnit.unit_spec]
      ring
    have hCinj := injective_toLin'_of_det_ne_zero C
      (by rw [hC]; exact mul_ne_zero (pow_ne_zero _ hϖ0) w.ne_zero)
    have hC'inj := injective_toLin'_of_det_ne_zero C'
      (by rw [hdetC']; exact mul_ne_zero (pow_ne_zero _ hϖ0) (Units.ne_zero _))
    have e1 := card_quot_range_comp (Matrix.toLin' C) (Matrix.toLin' P) hCinj
    have e2 := card_quot_range_comp (Matrix.toLin' C') (Matrix.toLin' (scaleAt i0 ϖ)) hC'inj
    rw [← Matrix.toLin'_mul, hCP, Matrix.toLin'_mul, e2,
      card_quot_range_of_isUnit_det P (by rw [hdetP]; exact hunit), one_mul,
      card_quot_range_scaleAt ϖ hϖ i0, ih C' _ hdetC'] at e1
    rw [← e1, pow_succ']

example {ι : Type*} [Fintype ι] [DecidableEq ι] (ϖ : O) (hϖ : Irreducible ϖ) (j : ι) :
    Nat.card ((ι → O) ⧸ LinearMap.range (Matrix.toLin' (scaleAt j ϖ))) =
      Nat.card (IsLocalRing.ResidueField O) ^ 1 :=
  card_quot_range_toLin_clean ϖ hϖ (scaleAt j ϖ) 1 1 (by rw [det_scaleAt]; simp)

end DVRLatticeIndex
