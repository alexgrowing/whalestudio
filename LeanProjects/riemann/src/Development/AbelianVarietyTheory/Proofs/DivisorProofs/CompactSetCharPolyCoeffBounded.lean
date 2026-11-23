import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.LocBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact (GlobalTheory.ConjAtPlace.cj_spec w h).1
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact continuous_id

theorem continuous_nrmL (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun y => y := funext fun y => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have e : nrmL n w = fun y => y * thetaGL n (cj w) y := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id.mul (GlobalTheory.ThetaPull.continuous_thetaGL (cj w) (continuous_cj w))

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem exists_bound_of_isCompact (w : Pl E) {K : Set (w.adicCompletion E)} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, Valued.v x ≤ WithZero.exp (m : ℤ) := by
  let U : ℕ → Set (w.adicCompletion E) := fun m => {y | Valued.v y ≤ WithZero.exp (m : ℤ)}
  have hcov : K ⊆ ⋃ m : ℕ, U m := by
    intro x _
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact Set.mem_iUnion.2 ⟨0, by simp only [U, Set.mem_setOf_eq, h0]; exact zero_le'⟩
    · refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v x ≤ _
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
  have hdir : Directed (· ⊆ ·) U :=
    Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 (by exact_mod_cast hab))
  obtain ⟨m, hm⟩ := hK.elim_directed_cover U (fun m => GlobalTheory.PrincCong.isOpen_ball w (m : ℤ)) hcov hdir
  exact ⟨m, fun x hx => hm hx⟩

theorem bound_charpoly_nrmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C →
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y ∈ C,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ γ) ∧
        γ⁻¹ ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) := by
  intro E _ _ _ n w C hC
  let F : Option (Fin (n + 1)) → GLw n w → w.adicCompletion E := fun o y =>
    match o with
    | none => ((nrmL n w y)⁻¹).val.det
    | some i => (nrmL n w y).val.charpoly.coeff i
  have hF : ∀ o, Continuous (F o) := by
    rintro (_ | i)
    · exact (Units.continuous_val.comp (continuous_nrmL n w).inv).matrix_det
    · exact (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (continuous_nrmL n w))
  have hK : IsCompact (⋃ o, F o '' C) := isCompact_iUnion fun o => hC.image (hF o)
  obtain ⟨m, hm⟩ := exists_bound_of_isCompact w hK
  have hb : ∀ o, ∀ y ∈ C, Valued.v (F o y) ≤ WithZero.exp (m : ℤ) := fun o y hy =>
    hm _ (Set.mem_iUnion.2 ⟨o, Set.mem_image_of_mem _ hy⟩)
  refine ⟨WithZero.exp (m : ℤ), WithZero.exp_ne_zero, fun y hy => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hi : i ≤ n
    · exact hb (some ⟨i, Nat.lt_succ_of_le hi⟩) y hy
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)]
      simp
  · have h1 : Valued.v (((nrmL n w y)⁻¹).val.det) ≤ WithZero.exp (m : ℤ) := hb none y hy
    have hdet : (nrmL n w y).val.det * ((nrmL n w y)⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hc0 : (nrmL n w y).val.charpoly.coeff 0 = (-1) ^ n * (nrmL n w y).val.det := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
        one_mul]
    have hv : Valued.v ((nrmL n w y).val.charpoly.coeff 0) * Valued.v (((nrmL n w y)⁻¹).val.det) = 1 := by
      rw [hc0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, ← map_mul, hdet, map_one]
    have hne : Valued.v (((nrmL n w y)⁻¹).val.det) ≠ 0 := fun h => by
      rw [h, mul_zero] at hv; exact zero_ne_one hv
    rw [eq_inv_of_mul_eq_one_left hv]
    exact inv_anti₀ (zero_lt_iff.2 hne) h1

end GlobalTheory.LocBound
