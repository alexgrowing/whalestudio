import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientSpanRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime

open IsLocalRing TensorProduct

namespace GlobalTheory.JacobianDerivation

theorem isRegularLocalRing_quotient : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T)
    (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) →
    (Matrix.of fun i j => D i (f j)).det ∉ n →
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  intro T _ _ h f D n _ hf hdet
  classical
  let A := Localization.AtPrime n
  haveI : IsRegularLocalRing A := IsRegularRing.isRegularLocalRing_localization n
  let x : Fin h → A := fun j => algebraMap T A (f j)
  have hx : ∀ j, x j ∈ maximalIdeal A := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A n (f j)).mpr (hf j)

  have hrow0 : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 →
      ∀ i, ∑ j, a j * algebraMap T A (D i (f j)) ∈ maximalIdeal A := by
    intro a ha i
    obtain ⟨D', hD'⟩ := @GlobalTheory.derivation_extend_localization_atPrime ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
      (@IsScalarTower.of_algebraMap_eq' ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
        (Subsingleton.elim _ _)) n _ _
      { toFun := fun t => algebraMap T A (D i t)
        map_add' := fun s t => by simp
        map_smul' := fun m t => by simp [Algebra.smul_def]
        map_one_eq_zero' := by simp
        leibniz' := fun s t => by simp [Algebra.smul_def] }
    letI : Algebra ℤ A := Ring.toIntAlgebra A
    have hsq : ∀ y ∈ maximalIdeal A ^ 2, D' y ∈ maximalIdeal A := by
      intro y hy
      rw [pow_two] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun y z hy hz => ?_)
      · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
      · rw [map_add]; exact Ideal.add_mem _ hy hz
    have h1 := hsq _ ha
    rw [map_sum] at h1
    have h2 : ∀ j, D' (a j * x j) = a j * algebraMap T A (D i (f j)) + x j * D' (a j) := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD']
      rfl
    simp_rw [h2, Finset.sum_add_distrib] at h1
    have h3 : ∑ j, x j * D' (a j) ∈ maximalIdeal A :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx j)
    simpa using Ideal.sub_mem _ h1 h3
  have hind : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 → ∀ j, a j ∈ maximalIdeal A := by
    intro a ha
    have hrow := hrow0 a ha
    let φ : T →+* ResidueField A := (residue A).comp (algebraMap T A)
    let M : Matrix (Fin h) (Fin h) (ResidueField A) := φ.mapMatrix (Matrix.of fun i j => D i (f j))
    have hM : M.det ≠ 0 := by
      rw [← RingHom.map_det]
      intro h0
      have hu : IsUnit (algebraMap T A (Matrix.of fun i j => D i (f j)).det) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A n _).mpr hdet
      exact (residue_ne_zero_iff_isUnit _).mpr hu h0
    have hv : M.mulVec (fun j => residue A (a j)) = 0 := by
      funext i
      have := (residue_eq_zero_iff _).mpr (hrow i)
      rw [map_sum] at this
      simp only [Matrix.mulVec, dotProduct, M, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply, φ, RingHom.comp_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
    intro j
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hv) j
    exact (residue_eq_zero_iff _).mp this

  let τ : Fin h → maximalIdeal A := fun i => ⟨x i, hx i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * x j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  have hrange : (Set.range fun i => ((τ i : maximalIdeal A) : A)) = Set.range x := rfl
  rw [hrange] at hs
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quot_regular A t x hs hd
  have hmap : (Ideal.span (Set.range f)).map (algebraMap T A) = Ideal.span (Set.range x) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  show IsRegularLocalRing (A ⧸ (Ideal.span (Set.range f)).map (algebraMap T A))
  rw [hmap]
  exact hreg

end GlobalTheory.JacobianDerivation
