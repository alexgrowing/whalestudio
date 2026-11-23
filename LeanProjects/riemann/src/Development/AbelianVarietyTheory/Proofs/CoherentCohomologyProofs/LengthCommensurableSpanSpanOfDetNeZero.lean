import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDualNeZeroCompEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientSpanSingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthSelfEqTop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Imports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearEquivMapLatticeEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SignedLengthOfCommonLower
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanEqAddValDet
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCokerOfNotInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SignedLengthSpanEqOrdFracDet
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanMatrix
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SignedLengthEqLogOrdFracDet
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SignedLengthMapEqLogOrdFracDet

open Module IsDiscreteValuationRing

namespace GlobalTheory

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section Cokernel

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem length_self_eq_top_of_dvr : Module.length R R = ⊤ := by
  by_contra h
  have h' := Module.length_ne_top_iff.mp h
  rw [← isArtinianRing_iff_isFiniteLength] at h'
  exact not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  first
  | (rename_i h_1 h_2 h_3; revert R h_1 h_2 h_3 ι s a; exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod)
  | exact @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod
  | (apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdditiveValuationProduct.addVal_prod <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdditiveValuationProduct.addVal_prod ..)

theorem length_quotient_range_eq_top_of_det_eq_zero [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (hf : LinearMap.det f = 0) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 f hf; exact @_root_.GlobalTheory.LengthDualFunctional.main)
  | exact @_root_.GlobalTheory.LengthDualFunctional.main
  | exact _root_.GlobalTheory.LengthDualFunctional.main
  | (apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthDualFunctional.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthDualFunctional.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthDualFunctional.main ..)

theorem length_quotient_eq_addVal_det_equiv [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) = addVal R (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_8; revert R h_1 h_2 h_3 M h_5 h_6 h_7 h_8 N e; exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det)
  | exact @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det ..)

theorem length_quotient_range_eq_addVal_det [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.det f = 0
  · rw [length_quotient_range_eq_top_of_det_eq_zero hf, hf, addVal_zero]
  · have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      by_contra h
      exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    exact length_quotient_eq_addVal_det_equiv _ (LinearEquiv.ofInjective f hinj)

theorem length_quotient_range_ne_top_iff [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} :
    Module.length R (M ⧸ LinearMap.range f) ≠ ⊤ ↔ LinearMap.det f ≠ 0 := by
  rw [length_quotient_range_eq_addVal_det, ne_eq, addVal_eq_top_iff]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem length_quotient_range_toLin'_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range (Matrix.toLin' P)) = addVal R P.det := by
  rw [length_quotient_range_eq_addVal_det, LinearMap.det_toLin']

theorem length_quotient_range_mulVecLin_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det :=
  length_quotient_range_toLin'_eq_addVal_det P

theorem length_quotient_span_cols_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ Submodule.span R (Set.range P.col)) = addVal R P.det := by
  rw [← Matrix.range_mulVecLin, length_quotient_range_mulVecLin_eq_addVal_det]

theorem length_quotient_span_rows_eq_addVal_det (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ Submodule.span R (Set.range P.row)) = addVal R P.det := by
  rw [← Matrix.det_transpose]
  exact length_quotient_span_cols_eq_addVal_det P.transpose

theorem length_quotient_range_eq_addVal_det_toMatrix {M' : Type*} [AddCommGroup M'] [Module R M']
    (b' : Basis ι R M') (b : Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.toMatrix b' b f).det := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9 h_11 h_12; revert R h_1 h_2 h_3 M h_5 h_6 ι h_8 h_9 M' h_11 h_12 b' b f; exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main)
  | exact @_root_.GlobalTheory.LengthQuotientSpanValuation.main
  | exact _root_.GlobalTheory.LengthQuotientSpanValuation.main
  | (apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthQuotientSpanValuation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthQuotientSpanValuation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthQuotientSpanValuation.main ..)

theorem length_quotient_span_eq_addVal_det (b : Basis ι R M) (v : ι → M) :
    Module.length R (M ⧸ Submodule.span R (Set.range v)) = addVal R (b.det v) := by
  rw [← b.constr_range R, length_quotient_range_eq_addVal_det_toMatrix b b, Basis.det_apply,
    Basis.toMatrix_eq_toMatrix_constr]
  rfl

theorem length_quotient_span_ne_top_iff (b : Basis ι R M) {v : ι → M} :
    Module.length R (M ⧸ Submodule.span R (Set.range v)) ≠ ⊤ ↔ b.det v ≠ 0 := by
  rw [length_quotient_span_eq_addVal_det b, ne_eq, addVal_eq_top_iff]

theorem length_quotient_span_eq_top_of_det_eq_zero (b : Basis ι R M) {v : ι → M}
    (hv : b.det v = 0) : Module.length R (M ⧸ Submodule.span R (Set.range v)) = ⊤ := by
  rw [length_quotient_span_eq_addVal_det b, hv, addVal_zero]

theorem length_quotient_eq_addVal_det_basis (b : Basis ι R M) (N : Submodule R M)
    (c : Basis ι R N) : Module.length R (M ⧸ N) = addVal R (b.det fun i => (c i : M)) := by
  rw [← length_quotient_span_eq_addVal_det]
  have : Submodule.span R (Set.range fun i => (c i : M)) = N := by
    conv_rhs => rw [← Submodule.map_subtype_top N, ← c.span_eq, Submodule.map_span,
      ← Set.range_comp]
    rfl
  rw [this]

end Cokernel

section Relative

variable {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem relLength_span_eq_addVal_det {A : Submodule R V} (b : Basis ι R A) (v : ι → A) :
    relLength A (Submodule.span R (Set.range fun i => (v i : V))) = addVal R (b.det v) := by
  have : Submodule.span R (Set.range fun i => (v i : V)) =
      (Submodule.span R (Set.range v)).map A.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← length_quotient_span_eq_addVal_det, ← relLength_top_left, ← relLength_map_subtype,
    Submodule.map_subtype_top, this]

theorem relLength_span_span_eq_addVal_det {a v : ι → V} (ha : LinearIndependent R a)
    (P : Matrix ι ι R) (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      addVal R P.det := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9; revert R h_1 h_2 h_3 V h_5 h_6 ι h_8 h_9 a v ha P hv; exact @_root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq)
  | exact @_root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq
  | exact _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq
  | (apply _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeLengthSpanDet.relLength_span_eq ..)

theorem relLength_map_eq_addVal_det_restrict {A : Submodule R V} [Module.Free R A]
    [Module.Finite R A] (g : V →ₗ[R] V) (hg : ∀ x ∈ A, g x ∈ A) :
    relLength A (A.map g) = addVal R (LinearMap.det (g.restrict hg)) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_8 h_9; revert R h_1 h_2 h_3 V h_5 h_6 A h_8 h_9 g hg; exact @_root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det)
  | exact @_root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det
  | exact _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det ..)

end Relative

section Lattice

private theorem relLength_chain {S V : Type*} [Ring S] [AddCommGroup V] [Module S V]
    {A B C : Submodule S V} (hAB : B ≤ A) (hBC : C ≤ B) :
    relLength A C = relLength A B + relLength B C := by
  rw [← relLength_map_mkQ hBC A, relLength_eq_length_map_mkQ A C, relLength_eq_length_map_mkQ B C,
    relLength_def, add_comm,
    ← (Submodule.submoduleOfEquivOfLe (Submodule.map_mono (f := C.mkQ) hAB)).length_eq]
  exact Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)

private theorem signedLength_of_common {S V : Type*} [Ring S] [AddCommGroup V] [Module S V]
    {A B C : Submodule S V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ} (hm : relLength A C = m)
    (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by
  first
  | (rename_i h_2 h_3 h_4; revert S V h_2 h_3 h_4 A B C hA hB m n hm hn; exact @_root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower)
  | exact @_root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower
  | exact _root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower
  | (apply _root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower ..)

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem ordFrac_algebraMap_eq_exp {x : R} {n : ℕ} (h : addVal R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R
    (mem_nonZeroDivisors_of_ne_zero hx) ((Ring.ord_eq_addVal x).trans h)]
  rfl

theorem ordFrac_unit_mul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) :
    Ring.ordFrac R (algebraMap R K u * algebraMap R K ϖ ^ n) = WithZero.exp n := by
  rw [map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible hϖ, one_mul,
    ← WithZero.exp_zsmul, smul_eq_mul, mul_one]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem lattice_length_ord_frac_det {a b : ι → V} (ha : LinearIndependent K a) (g : Matrix ι ι K)
    (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) ∧
      Ring.ordFrac R g.det = WithZero.exp
        (signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b))) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 a b ha g hg hb; exact @_root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det)
  | exact @_root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det
  | exact _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det
  | (apply _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det ..)

theorem lengthCommensurable_span_span_of_det_ne_zero {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) :=
  (lattice_length_ord_frac_det ha g hg hb).1

theorem ordFrac_det_eq_exp_signedLength_span {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    Ring.ordFrac R g.det = WithZero.exp
      (signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b))) :=
  (lattice_length_ord_frac_det ha g hg hb).2

theorem signedLength_span_eq_log_ordFrac_det {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) =
      WithZero.log (Ring.ordFrac R g.det) := by
  rw [ordFrac_det_eq_exp_signedLength_span ha g hg hb, WithZero.log_exp]

theorem signedLength_span_eq_log_ordFrac_det_generalLinear {a b : ι → V}
    (ha : LinearIndependent K a) (g : GL ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) ∧
      signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) =
        WithZero.log (Ring.ordFrac R (g : Matrix ι ι K).det) :=
  ⟨lengthCommensurable_span_span_of_det_ne_zero ha _ g.det_ne_zero hb,
    signedLength_span_eq_log_ordFrac_det ha _ g.det_ne_zero hb⟩

theorem signedLength_span_eq_of_det_eq_unit_mul_zpow {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ)
    (n : ℤ) (hg : g.det = algebraMap R K u * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 a b ha g hb ϖ hϖ u n hg; exact @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq)
  | exact @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq
  | exact _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq
  | (apply _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthTower.signedLength_span_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthTower.signedLength_span_eq ..)

theorem lengthCommensurable_span_basis (a b : Basis ι K V) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) :=
  lengthCommensurable_span_span_of_det_ne_zero a.linearIndependent (a.toMatrix b)
    (a.isUnit_det b).ne_zero fun j => (a.sum_toMatrix_smul_self b j).symm

theorem ordFrac_basis_det_eq_exp_signedLength (a b : Basis ι K V) :
    Ring.ordFrac R (a.det b) = WithZero.exp
      (signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b))) :=
  ordFrac_det_eq_exp_signedLength_span a.linearIndependent (a.toMatrix b)
    (a.isUnit_det b).ne_zero fun j => (a.sum_toMatrix_smul_self b j).symm

theorem signedLength_span_basis_eq_log_ordFrac_det (a b : Basis ι K V) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) =
      WithZero.log (Ring.ordFrac R (a.det b)) := by
  rw [ordFrac_basis_det_eq_exp_signedLength, WithZero.log_exp]

omit [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R] [Fintype ι] [DecidableEq ι] in
private theorem span_range_coe_basis {A : Submodule R V} (a : Basis ι R A) :
    Submodule.span R (Set.range fun i => (a i : V)) = A := by
  conv_rhs => rw [← Submodule.map_subtype_top A, ← a.span_eq, Submodule.map_span,
    ← Set.range_comp]
  rfl

omit [IsDiscreteValuationRing R] [Fintype ι] [DecidableEq ι] in
private theorem span_range_extendOfIsLattice {A : Submodule R V} [A.IsLattice K]
    (a : Basis ι R A) : Submodule.span R (Set.range (a.extendOfIsLattice K)) = A := by
  refine Eq.trans ?_ (span_range_coe_basis a)
  congr 2
  funext i
  exact a.extendOfIsLattice_apply K i

theorem signedLength_eq_log_ordFrac_det_of_bases {A B : Submodule R V} (a : Basis ι R A)
    (b : Basis ι R B) (g : Matrix ι ι K) (hg : g.det ≠ 0)
    (hb : ∀ j, (b j : V) = ∑ i, g i j • (a i : V)) :
    LengthCommensurable A B ∧ signedLength A B = WithZero.log (Ring.ordFrac R g.det) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 A B a b g hg hb; exact @_root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det)
  | exact @_root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det
  | exact _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det
  | (apply _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthLogDet.signedLength_eq_log_ordFrac_det ..)

theorem signedLength_map_eq_log_ordFrac_det (A : Submodule R V) [A.IsLattice K] (g : V →ₗ[K] V)
    (hg : LinearMap.det g ≠ 0) :
    LengthCommensurable A (A.map (g.restrictScalars R)) ∧
      signedLength A (A.map (g.restrictScalars R)) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g)) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 A h_14 g hg; exact @_root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det)
  | exact @_root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
  | exact _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
  | (apply _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det ..)

theorem signedLength_eq_log_ordFrac_det_of_map_eq {A B : Submodule R V} [A.IsLattice K]
    (g : V ≃ₗ[K] V) (h : A.map ((g : V →ₗ[K] V).restrictScalars R) = B) :
    LengthCommensurable A B ∧
      signedLength A B = WithZero.log (Ring.ordFrac R (LinearMap.det (g : V →ₗ[K] V))) :=
  h ▸ signedLength_map_eq_log_ordFrac_det A _ g.isUnit_det'.ne_zero

variable (K) in

theorem exists_linearEquiv_map_eq_of_isLattice (A B : Submodule R V) [A.IsLattice K]
    [B.IsLattice K] : ∃ g : V ≃ₗ[K] V, A.map ((g : V →ₗ[K] V).restrictScalars R) = B := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_15 h_16; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 A B h_15 h_16; exact @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq)
  | exact @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq
  | exact _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq
  | (apply _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq ..)

variable (K) in

theorem lengthCommensurable_of_isLattice (A B : Submodule R V) [A.IsLattice K] [B.IsLattice K] :
    LengthCommensurable A B :=
  have ⟨g, h⟩ := exists_linearEquiv_map_eq_of_isLattice K A B
  (signedLength_eq_log_ordFrac_det_of_map_eq g h).1

theorem valuation_det_eq_exp_neg_signedLength {A B : Submodule R V} [A.IsLattice K]
    (g : V ≃ₗ[K] V) (h : A.map ((g : V →ₗ[K] V).restrictScalars R) = B) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (LinearMap.det (g : V →ₗ[K] V)) =
      WithZero.exp (-signedLength A B) := by
  rw [(signedLength_eq_log_ordFrac_det_of_map_eq g h).2, WithZero.exp_neg,
    WithZero.exp_log ((map_ne_zero _).mpr g.isUnit_det'.ne_zero), Ring.ordFrac_eq_valuation_inv,
    inv_inv]

example {ϖ : R} (hϖ : Irreducible ϖ) :
    signedLength (Submodule.span R (Set.range fun _ : Unit => (1 : K)))
      (Submodule.span R (Set.range fun _ : Unit => (algebraMap R K ϖ)⁻¹)) = -1 :=
  signedLength_span_eq_of_det_eq_unit_mul_zpow (K := K) (by simp)
    (Matrix.of fun _ _ => (algebraMap R K ϖ)⁻¹) (by simp) hϖ 1 (-1) (by simp)

end Lattice

end GlobalTheory
