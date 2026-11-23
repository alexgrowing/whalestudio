import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThreeStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Sl2Ad

theorem form_isSymm {K : Type} [Field K] : (form (K := K)).IsSymm := by
  first
  | exact ⟨fun v w => by simp only [RingHom.id_apply, form_apply]; ring⟩
  | exact fun v w => by simp only [RingHom.id_apply, form_apply]; ring
  | (intro v w; simp only [RingHom.id_apply, form_apply]; ring)

theorem form_ad {K : Type} [Field K] (A : GL (Fin 2) K) (v w : Fin 3 → K) :
    form (ad A *ᵥ v) (ad A *ᵥ w) = form v w := by
  rw [← coord_conj_ofCoord, ← coord_conj_ofCoord,
    form_coord (by rw [trace_conj, trace_ofCoord]) (by rw [trace_conj, trace_ofCoord])]
  conv_rhs => rw [← coord_ofCoord v, ← coord_ofCoord w, form_coord (trace_ofCoord v) (trace_ofCoord w)]
  have : ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord w * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = (A : Matrix (Fin 2) (Fin 2) K) * (ofCoord v * ofCoord w) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h, Matrix.one_mul]
  rw [this, trace_conj]

theorem form_nondegenerate {K : Type} [Field K] [CharZero K] : (form (K := K)).Nondegenerate := by
  rw [form, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  simp [Matrix.det_fin_three]

theorem coord_smul_scalar {F K : Type} [Field F] [Field K] [Algebra F K] (a : F) (X : Matrix (Fin 2) (Fin 2) K) :
    coord (a • X) = a • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_sum {K : Type} [Field K] {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) K) :
    coord (∑ i ∈ s, f i) = ∑ i ∈ s, coord (f i) := by
  ext j; fin_cases j <;> simp [coord, Matrix.sum_apply]

end GlobalTheory.Sl2Ad

open GlobalTheory.Sl2Ad in

theorem GlobalTheory.Sl2Ad.augmentation_contains_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  intro l _ c Γ _ r _ hirr
  set S : Γ →* Matrix (Fin 3) (Fin 3) (Qbar l) := adHom.comp r with hS
  have hSg : ∀ g, S g = ad (r g) := fun g => rfl
  have h1 := GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three S form form_nondegenerate form_isSymm (fun g v w => form_ad _ v w)
    (fun v hv => GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr r hirr v (fun g => by rw [← hSg]; exact hv g))
    (fun y hy hy' => GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible r hirr y hy (fun g => by rw [← hSg]; exact hy' g))
  obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp h1
  choose γ hγ using fun i => (g i).2
  have hdet : (∑ i, b i • (S (γ i) - 1)).det ≠ 0 := by
    have : ∑ i, b i • (S (γ i) - 1) = 1 :=
      (Finset.sum_congr rfl fun i _ => by rw [← hγ i]).trans hg
    rw [this, Matrix.det_one]; exact one_ne_zero
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero (fun i => S (γ i) - 1) b hdet
  set J : Submodule ℚ_[l] (Matrix (Fin 3) (Fin 3) (Qbar l)) := Submodule.span ℚ_[l] (Set.range fun g => S g - 1) with hJ
  have hmul : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        have : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
          rw [map_mul]; noncomm_ring
        rw [this]
        exact J.sub_mem (J.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [mul_zero]; exact J.zero_mem
      | add y z _ _ hy hz => rw [mul_add]; exact J.add_mem hy hz
      | smul t y _ hy => rw [mul_smul_comm]; exact J.smul_mem t hy
    | zero => rw [zero_mul]; exact J.zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact J.add_mem hx hz
    | smul t x _ hx => rw [smul_mul_assoc]; exact J.smul_mem t hx
  have hT : (∑ i, (a i : Qbar l) • (S (γ i) - 1)) ∈ J := by
    refine J.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact J.nsmul_mem (Submodule.subset_span ⟨_, rfl⟩) _
  have hone := GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero J hmul _ hT ha
  obtain ⟨n', a', g', hg'⟩ := Submodule.mem_span_set'.mp hone
  choose γ' hγ' using fun i => (g' i).2
  refine ⟨n', γ', a', fun X hX => ?_⟩
  have htr : (∑ i, a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) - X)).trace = 0 := by
    rw [Matrix.trace_sum]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_conj, hX, sub_zero, smul_zero]
  refine ((ofCoord_coord hX).symm.trans ?_).trans (ofCoord_coord htr)
  congr 1
  rw [coord_sum]
  have : ∀ i, coord (a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X))
      = (a' i • (S (γ' i) - 1)) *ᵥ coord X := by
    intro i
    rw [coord_smul_scalar, show ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X)
      = (r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) + (-1 : Qbar l) • X by
        rw [neg_one_smul, ← sub_eq_add_neg], coord_add, coord_conj _ hX, coord_smul, hSg, Matrix.smul_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, neg_one_smul, ← sub_eq_add_neg]
  simp_rw [this, ← Matrix.sum_mulVec]
  have e : ∑ i, a' i • (S (γ' i) - 1) = 1 :=
    (Finset.sum_congr rfl fun i _ => by rw [← hγ' i]).trans hg'
  rw [e, Matrix.one_mulVec]
