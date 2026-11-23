import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DualBetaReferenceCongruence

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AlgL

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [dotProduct, hrow, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

private lemma vecMulVec_mulVec_rank_two_dimension_formula (u v y : Fin n → A) : Matrix.vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext q
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  rw [sMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_rank_two_dimension_formula,
    vecMulVec_mulVec_rank_two_dimension_formula, hrow_dot, hrow_dot, smul_smul, smul_smul]

end AlgL

section Main

variable {D : D7} {X : HidaSetting D}

theorem tmul_one_mem {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) :
    ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)

theorem resT_congr (TR : TypedRed X) (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) (hZ : ZMod' X.B.I X.B.g (x - y)) : resT TR v x = resT TR v y := by
  obtain ⟨t, ht, hxy⟩ := hZ
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem _ _
  have hgt : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t ∈ IntAf X.B.I.F X.B.I.E :=
    (IntAf X.B.I.F X.B.I.E).mul_mem hg ht
  have hx : x = y + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := sub_eq_iff_eq_add'.1 hxy
  have hxm : x ∈ IntAf X.B.I.F X.B.I.E := hx ▸ (IntAf X.B.I.F X.B.I.E).add_mem hy hgt
  have h0 : TR.res v ⟨_, hgt⟩ = 0 := by
    refine (TR.res_ker ⟨_, hgt⟩).2 ?_ v
    exact ⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, mul_left_comm _ _ _⟩
  have hsplit : (⟨x, hxm⟩ : IntAf X.B.I.F X.B.I.E) = ⟨y, hy⟩ + ⟨_, hgt⟩ := Subtype.ext hx
  simp only [resT, dif_pos hxm, dif_pos hy]
  rw [hsplit, map_add, h0, add_zero]

theorem idxDLevi : IdxDLevi := by
  intro D X TR e he b bs hF hL hC C C' _ hCint v i j
  have hew := X.ew_int
  have hbwd : ∀ l, X.bwd l ∈ X.B.I.Lf := fun l => (X.vectorsInLattice.2.2 l).2
  have he1 : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E := tmul_one_mem he.1
  have hεint : epsX X e * C i j ∈ IntAf X.B.I.F X.B.I.E := mul_mem (mul_mem he1 hew) (hCint i j).1
  apply resT_congr TR v hεint
  have hh : ∀ x y : VA X.B.I, Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x y = hA X.B.I x y := fun _ _ => rfl
  have hsig1 : sigA X.B.I ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
    rw [unitaryCongruence.sigA_tmul, star_one]
  have hzero : ∀ q, hA X.B.I (b q) (X.bw j) = 0 := by
    intro q
    rw [hF.2.2.1 q, X.bw_w j, unitaryCongruence.hA_smul_left, unitaryCongruence.hA_smul_right]
    unfold epsX
    rw [map_mul, hsig1]
    have := X.ew_orth
    linear_combination ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * hA X.B.I (b q) (X.bw j) * this
  have hexp : hA X.B.I (X.bwd i) (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j) =
      hA X.B.I (X.bwd i) (X.bw j) +
        ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) := by
    rw [sMat_mulVec]
    simp only [hh]
    rw [← unitaryCongruence.hL_apply]
    simp only [map_add, map_sum, map_smul, unitaryCongruence.hL_apply, smul_eq_mul, hzero, mul_zero, zero_mul,
      add_zero]
  rw [hexp]
  have hCm : ∀ p q, (C - 1) p q ∈ IntAf X.B.I.F X.B.I.E := by
    intro p q
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem (hCint p q).1 ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  set S1 := ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) with hS1
  set S2 := ∑ p, ∑ q, (C - 1) p q * ((if q = j then X.ew else 0) * (if i = p then X.ew else 0)) with hS2
  have key1 : ZMod' X.B.I X.B.g (S1 - S2) := by
    have eq : S1 - S2 = ∑ p, ∑ q, (C - 1) p q * (hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0)) := by
      rw [hS1, hS2]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eq]
    refine unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun p _ => unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun q _ => ?_
    refine unitaryCongruence.Z_smul X.B.I X.B.g (hCm p q) ?_
    have eq2 : hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0) =
        hA X.B.I (X.bwd i) (b p) * (hA X.B.I (bs q) (X.bw j) - if q = j then X.ew else 0) +
        (if q = j then X.ew else 0) * (hA X.B.I (X.bwd i) (b p) - if i = p then X.ew else 0) := by ring
    rw [eq2]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g
      (unitaryCongruence.hA_int X.B.I (hbwd i) (hL p).1) (hC q j).1) (unitaryCongruence.Z_smul X.B.I X.B.g ?_ (hC i p).2)
    split_ifs
    · exact hew
    · exact zero_mem _
  have hsum : S2 = (C - 1) i j * X.ew := by
    rw [hS2]
    simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', X.ew_idem]
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have hlast : ZMod' X.B.I X.B.g ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by
    refine ⟨((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * X.ew * C i j,
      mul_mem (mul_mem (tmul_one_mem ht) hew) (hCint i j).1, ?_⟩
    have hg : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((X.B.g : Af X.B.I.F)) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [← Algebra.TensorProduct.includeRight_apply (R := X.B.I.F) (A := X.B.I.E), map_natCast]
    have h1 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [het, ← hg, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) = 1 - (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
      rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
    have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e =
        1 - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [← h1, h2]; ring
    unfold epsX
    rw [Matrix.sub_apply, Matrix.one_apply, h3]
    split_ifs <;> ring
  have eqF : hA X.B.I (X.bwd i) (X.bw j) + S1 - epsX X e * C i j =
      (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (S1 - S2) + (S2 - (C - 1) i j * X.ew) +
        ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by ring
  have h0 : S2 - (C - 1) i j * X.ew = 0 := by rw [hsum, sub_self]
  rw [eqF, h0, add_zero]
  exact unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g (X.bw_dual i j) key1) hlast

end Main

end PI.UnitaryDimensionFormula
