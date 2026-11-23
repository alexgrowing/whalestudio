import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusCommStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EnvShape

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A]

theorem C_mem_supp (S : Set ℕ) (c : A) : MvPolynomial.C c ∈ MvPolynomial.supported A S := by
  rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ c

omit hl in

theorem cc_mem_ideal {R : Type} [CommRing R] (I : Ideal R) {x : R} (y : R) (hx : x ∈ I) : cc l x y ∈ I := by
  unfold cc
  exact Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx k (Finset.mem_Ioo.1 hk).1))

omit hl in

theorem cc_mem_sub {R : Type} [CommRing R] [Algebra A R] (S : Subalgebra A R) {x y : R} (hx : x ∈ S)
    (hy : y ∈ S) : cc l x y ∈ S := by
  unfold cc
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hx _)) (S.pow_mem hy _)

theorem phi_mem (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) {e : A} (he : e ∈ J) : D.φ e ∈ J := by
  rw [D.φ_eq]; exact J.add_mem (J.pow_mem_of_mem he _ hl.out.pos) (J.mul_mem_right _ hlJ)

theorem delta_Iio (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) (i : ℕ) (s : MvPolynomial ℕ A)
    (hs : s ∈ MvPolynomial.supported A (Set.Iio i)) :
    (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic i) ∧
    ∃ a ∈ MvPolynomial.supported A (Set.Iio i), ∃ b ∈ MvPolynomial.supported A (Set.Iio i),
      (polyDelta D).δ s - (a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  cases i with
  | zero =>
    have h0 : Set.Iio (0:ℕ) = ∅ := by ext; simp
    rw [h0, MvPolynomial.supported_empty, Algebra.mem_bot] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨C_mem_supp _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ c), C_mem_supp _ _, ?_⟩
    simp
  | succ i =>
    have h1 : Set.Iio (i+1) = Set.Iic i := by ext; simp [Nat.lt_succ_iff]
    rw [h1] at hs ⊢
    obtain ⟨h2, a, ha, b, hb, h3⟩ := GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime l A D i s hs
    have hl' : (l : MvPolynomial ℕ A) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial ℕ A) hlJ
      rwa [map_natCast] at this
    exact ⟨h2, a, ha, b, hb, Ideal.span_le.2 (Set.singleton_subset_iff.2 hl') h3⟩

theorem step_eq (D : Delta l A) (e : A) (k : ℕ) (s : MvPolynomial ℕ A) :
    (polyDelta D).δ (MvPolynomial.C e * MvPolynomial.X k + s) =
      MvPolynomial.C (D.φ e) * MvPolynomial.X (k + 1) +
        (MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
          cc l (MvPolynomial.C e * MvPolynomial.X k) s) := by
  rw [(polyDelta D).δ_add, (polyDelta D).δ_mul, polyDelta_C, polyDelta_X, D.φ_eq]
  simp only [map_add, map_pow, map_mul, map_natCast]
  unfold cc; ring

theorem shape (D : Delta l A) (J : Ideal A) (d p : A) (hlJ : (l : A) ∈ J) (hd : d ∈ J)
    (hu : IsUnit (D.δ d)) (k : ℕ) :
    ∃ e ∈ J, IsUnit (D.δ e) ∧ ∃ s ∈ MvPolynomial.supported A (Set.Iio k),
      (polyDelta D).δ^[k] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) =
        MvPolynomial.C e * MvPolynomial.X k + s := by
  induction k with
  | zero => exact ⟨d, hd, hu, MvPolynomial.C p, C_mem_supp _ _, by simp [add_comm]⟩
  | succ k ih =>
    obtain ⟨e, he, heu, s, hs, hk⟩ := ih
    have hIic : Set.Iic k = Set.Iio (k+1) := by ext; simp [Nat.lt_succ_iff]
    have hX : MvPolynomial.X k ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      by rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨k, by simp, rfl⟩
    have hδ := (delta_Iio D J hlJ k s hs).1
    rw [hIic] at hδ
    have hs' : s ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      MvPolynomial.supported_mono (Set.Iio_subset_Iio (Nat.le_succ k)) hs
    refine ⟨D.φ e, phi_mem D J hlJ he, ?_, MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
      cc l (MvPolynomial.C e * MvPolynomial.X k) s, ?_, ?_⟩
    · rw [GlobalTheory.T.deltaRingStructure_delta_frobenius_comm]; exact heu.map D.φ
    · exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hX _)
        (C_mem_supp _ _)) hδ) (cc_mem_sub _ (Subalgebra.mul_mem _ (C_mem_supp _ _) hX) hs')
    · rw [Function.iterate_succ_apply', hk, step_eq]

theorem envRel_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A),
    a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧
    envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈
      J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  intro l _ A _ D J d p hlJ hd hu i
  obtain ⟨e, he, heu, s, hs, hi⟩ := shape D J d p hlJ hd hu i
  obtain ⟨-, a, ha, b, hb, hab⟩ := delta_Iio D J hlJ i s hs
  refine ⟨heu.unit, a, b, ha, hb, ?_⟩
  have hrel : envRel D d p i = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) +
      (MvPolynomial.X i ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s) := by
    rw [envRel, Function.iterate_succ_apply', hi, step_eq]
  have hdiff : envRel D d p i - (MvPolynomial.C (heu.unit : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) + ((polyDelta D).δ s - (a * MvPolynomial.X i + b)) -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s := by
    rw [hrel, IsUnit.unit_spec]; ring
  rw [hdiff]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (phi_mem D J hlJ he))) hab)
    (cc_mem_ideal _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)))

end GlobalTheory.EnvShape
