import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

open Polynomial

namespace GlobalTheory.JR.Et.Idem

theorem isIntegral_of_forall {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem isIntegral_single {O : Type} [CommRing O] {ι : Type} [Finite ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (i : ι) (z : R i) (hz : IsIntegral O z) :
    IsIntegral O (Pi.single i z : ∀ j, R j) := by
  refine isIntegral_of_forall _ fun j => ?_
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero

theorem single_mul_single_of_ne {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroClass (R i)] {i j : ι}
    (h : i ≠ j) (a : R i) (b : R j) : (Pi.single i a : ∀ k, R k) * Pi.single j b = 0 := by
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk; rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hk, zero_mul]

theorem single_one_mul {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (x : ∀ j, R j) : (Pi.single i 1 : ∀ j, R j) * x = Pi.single i (x i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] [IsUltrametricDist F] (A : Et F E),
    (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
      IsIntegral (NormedField.valuation (K := F)).integer y ∨
        IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) →
    ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧
      (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧
      ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  intro F E _ _ _ _ _ _ A hval
  classical
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  let ψ : A.K ≃ₐ[F] (∀ I : MaximalSpectrum A.K, A.K ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A.K).restrictScalars F
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (MaximalSpectrum A.K)
  let f : Fin m → A.K := fun i => ψ.symm (Pi.single (e.symm i) 1)
  have hf : ∀ i, ψ (f i) = Pi.single (e.symm i) 1 := fun i => ψ.apply_symm_apply _
  haveI : Fintype (MaximalSpectrum A.K) := Fintype.ofFinite _
  have hOK : ∀ x : (∀ I : MaximalSpectrum A.K, A.K ⧸ I.asIdeal),
      IsIntegral (NormedField.valuation (K := F)).integer x → ψ.symm x ∈ A.OK := fun x hx =>
    (mem_OK_iff_isIntegral A _).2 (hx.map (ψ.symm.restrictScalars (NormedField.valuation (K := F)).integer))
  refine ⟨m, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ψ.injective
    rw [map_mul, hf, ← Pi.single_mul, mul_one]
  · intro i j hij
    apply ψ.injective
    rw [map_mul, hf, hf, map_zero]
    exact single_mul_single_of_ne (e.symm.injective.ne hij) _ _
  · apply ψ.injective
    rw [map_sum, map_one]
    simp_rw [hf]
    rw [Equiv.sum_comp e.symm (fun I => (Pi.single I 1 : ∀ J : MaximalSpectrum A.K, A.K ⧸ J.asIdeal))]
    exact Finset.univ_sum_single 1
  · intro i c hc h
    rw [mem_OK_iff_isIntegral] at h
    haveI := (e.symm i).isMaximal
    letI : Field (A.K ⧸ (e.symm i).asIdeal) := Ideal.Quotient.field _
    have h1 := h.map (((Pi.evalAlgHom F (fun J : MaximalSpectrum A.K => A.K ⧸ J.asIdeal) (e.symm i)).comp
      ψ.toAlgHom).restrictScalars (NormedField.valuation (K := F)).integer)
    have h2 : (((Pi.evalAlgHom F (fun J : MaximalSpectrum A.K => A.K ⧸ J.asIdeal) (e.symm i)).comp
      ψ.toAlgHom).restrictScalars (NormedField.valuation (K := F)).integer) (algebraMap F A.K c * f i) =
        algebraMap F (A.K ⧸ (e.symm i).asIdeal) c := by
      change ψ (algebraMap F A.K c * f i) (e.symm i) = _
      rw [map_mul, AlgEquiv.commutes, hf, Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.algebraMap_apply]
    rw [h2] at h1
    have h3 := (isIntegral_algebraMap_iff (algebraMap F (A.K ⧸ (e.symm i).asIdeal)).injective).1 h1
    have h4 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h3
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h4
    have h5 : ‖c‖ ≤ 1 := by exact_mod_cast h4
    linarith
  · intro i y hy
    haveI := (e.symm i).isMaximal
    letI : Field (A.K ⧸ (e.symm i).asIdeal) := Ideal.Quotient.field _
    haveI : FiniteDimensional F (A.K ⧸ (e.symm i).asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F (e.symm i).asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hfy : ψ (f i * y) = Pi.single (e.symm i) (ψ y (e.symm i)) := by
      rw [map_mul, hf, single_one_mul]
    have hfy' : f i * y = ψ.symm (Pi.single (e.symm i) (ψ y (e.symm i))) := by
      rw [← hfy, ψ.symm_apply_apply]
    by_cases hz : ψ y (e.symm i) = 0
    · exact absurd (by rw [hfy', hz, Pi.single_zero, map_zero]; exact (mem_OK_iff_isIntegral A 0).2 isIntegral_zero) hy
    rcases hval (A.K ⧸ (e.symm i).asIdeal) (ψ y (e.symm i)) hz with h | h
    · exact absurd (by rw [hfy']; exact hOK _ (isIntegral_single _ _ h)) hy
    · refine ⟨ψ.symm (Pi.single (e.symm i) (ψ y (e.symm i))⁻¹), hOK _ (isIntegral_single _ _ h), ?_⟩
      apply ψ.injective
      rw [map_mul, ψ.apply_symm_apply, hfy, hf, ← Pi.single_mul, inv_mul_cancel₀ hz]

end GlobalTheory.JR.Et.Idem
