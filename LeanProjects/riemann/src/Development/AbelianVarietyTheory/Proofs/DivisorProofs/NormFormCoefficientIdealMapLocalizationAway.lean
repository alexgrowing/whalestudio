import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheaf

theorem normForm_coeff_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (y : Fin m → L) (c : K) (s : Fin m →₀ ℕ) :
    (normForm K L (fun i => algebraMap K L c * y i)).coeff s =
      c ^ Module.finrank K L * (normForm K L y).coeff s := by
  have hM : ∀ i, (Algebra.leftMulMatrix (Module.finBasis K L) (algebraMap K L c * y i)).map
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) =
      (MvPolynomial.C c : MvPolynomial (Fin m) K) • (Algebra.leftMulMatrix (Module.finBasis K L) (y i)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, MvPolynomial.C_mul]
  have : normForm K L (fun i => algebraMap K L c * y i) =
      MvPolynomial.C (c ^ Module.finrank K L) * normForm K L y := by
    unfold normForm
    simp_rw [hM, smul_comm (MvPolynomial.X _ : MvPolynomial (Fin m) K) (MvPolynomial.C c), ← Finset.smul_sum,
      Matrix.det_smul, Fintype.card_fin, map_pow]
  rw [this, MvPolynomial.coeff_C_mul]

end GlobalTheory.NormSheaf

namespace GlobalTheory.NormSheaf

theorem normIdeal_map_away : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  intro A K L B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ h1 h2 h3 hinj hcoef J
  have e1 : ∀ x : A, algebraMap A' K (algebraMap A A' x) = algebraMap A K x := fun x => by
    simpa using RingHom.congr_fun h1 x
  have e2 : ∀ x : B, algebraMap B' L (algebraMap B B' x) = algebraMap B L x := fun x => by
    simpa using RingHom.congr_fun h2 x
  have e3 : ∀ x : A, algebraMap K L (algebraMap A K x) = algebraMap B L (algebraMap A B x) := fun x => by
    simpa using RingHom.congr_fun h3 x
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    unfold normIdeal
    rw [Ideal.span_le]
    rintro a ⟨m, g, hg, s, hs⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨m, fun i => algebraMap B B' (g i), fun i => Ideal.mem_map_of_mem _ (hg i), s, ?_⟩
    rw [e1, hs]
    simp only [e2]
  · unfold normIdeal
    rw [Ideal.span_le]
    rintro a' ⟨m, g', hg', s, hs⟩
    set b := algebraMap A B f with hb
    have hloc : ∀ i, ∃ (j : B) (n : ℕ), j ∈ J ∧ g' i * algebraMap B B' (b ^ n) = algebraMap B B' j := by
      intro i
      obtain ⟨⟨⟨j, hj⟩, ⟨_, n, rfl⟩⟩, h⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) B').1 (hg' i)
      exact ⟨j, n, hj, h⟩
    choose j n hj hn using hloc
    set N := ∑ i, n i
    have hN : ∀ i, g' i * algebraMap B B' (b ^ N) = algebraMap B B' (j i * b ^ (N - n i)) := by
      intro i
      have hle : n i ≤ N := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ i)
      rw [← Nat.add_sub_cancel' hle, pow_add, map_mul, ← mul_assoc, hn i, Nat.add_sub_cancel_left, map_mul]
    have hjJ : ∀ i, j i * b ^ (N - n i) ∈ J := fun i => J.mul_mem_right _ (hj i)
    set c := algebraMap A K f
    have himg : ∀ i, algebraMap B L (j i * b ^ (N - n i)) =
        algebraMap K L (c ^ N) * algebraMap B' L (g' i) := by
      intro i
      rw [← e2, ← hN i, map_mul, e2, map_pow, map_pow, hb, ← e3, mul_comm]
    obtain ⟨a, ha⟩ := hcoef (fun i => j i * b ^ (N - n i)) s
    have hcoef' : algebraMap A K a = (c ^ N) ^ Module.finrank K L * algebraMap A' K a' := by
      rw [ha, hs]
      simp only [himg]
      exact normForm_coeff_smul K L _ _ s
    have hmem : a ∈ normIdeal A K L B J := Ideal.subset_span ⟨m, _, hjJ, s, ha⟩
    have key : algebraMap A A' a = algebraMap A A' (f ^ (N * Module.finrank K L)) * a' := by
      apply hinj
      rw [map_mul, e1, e1, hcoef', map_pow, pow_mul]
    have hu : IsUnit (algebraMap A A' (f ^ (N * Module.finrank K L))) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hu, ← key]
    exact Ideal.mem_map_of_mem _ hmem

end GlobalTheory.NormSheaf
