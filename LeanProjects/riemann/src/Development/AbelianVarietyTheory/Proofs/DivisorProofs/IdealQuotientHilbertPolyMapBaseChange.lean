import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.MvPolynomialIsHomogeneousComapWeighted

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.HilbBaseChange

open Module TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] (n : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent n (MvPolynomial.map (algebraMap K L) p) =
      MvPolynomial.map (algebraMap K L) (homogeneousComponent n p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_mem_span_map_homogeneous {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    {g : MvPolynomial σ L}
    (hg : g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))))
    (n : ℕ) :
    homogeneousComponent n g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
      ((P.restrictScalars K ⊓ homogeneousSubmodule σ K n : Submodule K (MvPolynomial σ K)) :
        Set (MvPolynomial σ K))) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, rfl⟩ := hy
    rw [homogeneousComponent_map_algebraMap]
    exact Submodule.subset_span ⟨_, ⟨hP q hq n, homogeneousComponent_mem n q⟩, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem mem_span_image_of_mem_ideal_map {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) {g : MvPolynomial σ L}
    (hg : g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)) :
    g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) := by
  obtain ⟨M, hM⟩ : ∃ M : Submodule L (MvPolynomial σ L),
      M = Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) :=
    ⟨_, rfl⟩
  rw [← hM]
  have hX : ∀ (i : σ) (x : MvPolynomial σ L), x ∈ M → X i * x ∈ M := by
    intro i x hx
    rw [hM] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      refine Submodule.subset_span ⟨X i * q, P.mul_mem_left _ hq, ?_⟩
      simp
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hmul : ∀ (a x : MvPolynomial σ L), x ∈ M → a * x ∈ M := by
    intro a x hx
    induction a using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.C_mul']; exact M.smul_mem c hx
    | add p q hp hq => rw [add_mul]; exact M.add_mem hp hq
    | mul_X p i hp =>
      rw [show p * X i * x = X i * (p * x) by ring]
      exact hX i _ hp
  induction hg using Submodule.span_induction with
  | mem y hy => rw [hM]; exact Submodule.subset_span hy
  | zero => exact M.zero_mem
  | add y z _ _ hy hz => exact M.add_mem hy hz
  | smul a y _ hy => exact hmul a y hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem decompose_coe_eq_homogeneousComponent {σ L : Type} [Field L]
    (g : MvPolynomial σ L) (n : ℕ) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
    (((DirectSum.decompose (homogeneousSubmodule σ L)) g) n : MvPolynomial σ L) =
      homogeneousComponent n g := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single n]
    · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
    · intro i _ hi
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
    · intro h; exact absurd hn h
  · rw [homogeneousComponent_eq_zero]
    · refine Finset.sum_eq_zero fun i hi => ?_
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) (by rintro rfl; exact hn hi)
    · simp at hn; omega

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem linearIndependent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} {v : ι → MvPolynomial σ K}
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => MvPolynomial.map (algebraMap K L) (v i)) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := L) hv
  have h2 := h.map' (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap
    (algebraTensorAlgEquiv K L).toLinearEquiv.ker
  have he : (fun i => MvPolynomial.map (algebraMap K L) (v i)) =
      (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap ∘ fun i => (1 : L) ⊗ₜ[K] v i := by
    funext i
    simp [algebraTensorAlgEquiv_tmul]
  rw [he]
  exact h2

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem finrank_span_map_algebraMap_eq {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (W : Submodule K (MvPolynomial σ K)) [FiniteDimensional K W] :
    Module.finrank L (Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K)))) =
      Module.finrank K W := by
  let b := Module.finBasis K W
  let v : Fin (Module.finrank K W) → MvPolynomial σ L :=
    fun i => MvPolynomial.map (algebraMap K L) (b i : MvPolynomial σ K)
  have hli : LinearIndependent L v :=
    linearIndependent_map_algebraMap (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
  have hspan : Submodule.span L (Set.range v) =
      Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K))) := by
    apply le_antisymm
    · refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (b i).2, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw' : (⟨w, hw⟩ : W) ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
      have key : ∀ x : W, x ∈ Submodule.span K (Set.range b) →
          MvPolynomial.map (algebraMap K L) (x : MvPolynomial σ K) ∈
            (Submodule.span L (Set.range v)).restrictScalars K := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          have : MvPolynomial.map (algebraMap K L) ((c • y : W) : MvPolynomial σ K) =
              c • MvPolynomial.map (algebraMap K L) (y : MvPolynomial σ K) := by
            simp [MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
          rw [this]
          exact Submodule.smul_mem _ c hy
      exact key _ hw'
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem _root_.GlobalTheory.HilbBaseChange.idealHilbertPoly_map : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ _root_.GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = _root_.GlobalTheory.idealHilbertPoly P := by
  intro K L _ _ _ N P hP
  have hW : ∀ n : ℕ,
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).restrictScalars L ⊓
          homogeneousSubmodule (Fin N) L n =
        Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
          ((P.restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K (MvPolynomial (Fin N) K)) :
            Set (MvPolynomial (Fin N) K))) := by
    intro n
    apply le_antisymm
    · rintro g ⟨hg1, hg2⟩
      have := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg1) n
      rwa [homogeneousComponent_of_mem hg2, if_pos rfl] at this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      exact ⟨Ideal.mem_map_of_mem _ hw1,
        (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hw2).map _)⟩
  have hA : ∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L),
      ∀ n : ℕ, homogeneousComponent n g ∈
        P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) := by
    intro g hg n
    have h := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg) n
    rw [← hW n] at h
    exact h.1
  refine ⟨hA, ?_⟩
  have hhomP : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hP r hr i
  have hhomQ : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) L)
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hA r hr i
  have hdim : ∀ n : ℕ,
      Module.finrank L (_root_.GlobalTheory.quotPiece
        (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) (n : ℤ)) =
      Module.finrank K (_root_.GlobalTheory.quotPiece P (n : ℤ)) := by
    intro n
    have h1 := _root_.GlobalTheory.finrank_quotPiece_add
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) n
    have h2 := _root_.GlobalTheory.finrank_quotPiece_add P n
    rw [hW n, finrank_span_map_algebraMap_eq, _root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h1
    rw [_root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h2
    omega
  obtain ⟨n₀, hn₀⟩ := ((_root_.GlobalTheory.eventually_finrank_quotPiece hhomQ).and
    (_root_.GlobalTheory.eventually_finrank_quotPiece hhomP)).exists_forall_of_atTop
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
  · intro a b h
    simpa using h
  · intro m
    obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (by omega)
    simp only [Set.mem_setOf_eq]
    rw [← h1, ← h2, hdim]

end GlobalTheory.HilbBaseChange
