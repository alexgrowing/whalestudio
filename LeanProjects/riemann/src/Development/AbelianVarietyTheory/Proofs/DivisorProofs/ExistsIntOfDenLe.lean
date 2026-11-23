import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedImageInFinitelyGeneratedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsRealIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorSquaredBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicDenominatorBound

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

variable {p : ℕ} [Fact p.Prime]

theorem exists_int_of_den_le (D k : ℕ) (hD : 0 < D) (q : ℚ)
    (h1 : ∀ ℓ : ℕ, ℓ ≠ p → q.den.factorization ℓ ≤ D.factorization ℓ) (h2 : q.den.factorization p ≤ k) :
    ∃ m : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = m := by
  have hp : p.Prime := Fact.out
  have hN : 0 < D * p ^ k := Nat.mul_pos hD (pow_pos hp.pos k)
  have hdvd : q.den ∣ D * p ^ k := by
    rw [← Nat.factorization_le_iff_dvd q.den_nz hN.ne']
    intro ℓ
    rw [Nat.factorization_mul hD.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow, hp.factorization]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hl : ℓ = p
    · subst hl; simp only [Finsupp.single_eq_same, mul_one]; have := h2; omega
    · have := h1 ℓ hl; omega
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c * q.num, ?_⟩
  rw [hc]
  calc ((q.den * c : ℕ) : ℚ) * q = (c : ℚ) * (q * q.den) := by push_cast; ring
    _ = _ := by rw [Rat.mul_den_eq_num]; push_cast; ring

theorem grp_val_injective (G : HTGroup p) (β : G.Cˣ) :
    Function.Injective (fun y : grp G β => (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
  intro y y' hyy
  have hu : (y : G.Cˣ × ℚˣ).1 = (y' : G.Cˣ × ℚˣ).1 := Units.ext hyy
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y.2.1
  have h2 : (((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y'.2.1
  rw [hu] at h1
  have h3 : algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := by
    have := h1.symm.trans h2
    simpa using congrArg (· * ((β⁻¹ : G.Cˣ) : G.C)) this
  have h4 : (y : G.Cˣ × ℚˣ).2 = (y' : G.Cˣ × ℚˣ).2 := Units.ext ((algebraMap ℚ G.C).injective h3)
  exact Subtype.ext (Prod.ext hu h4)

theorem finite_fix_core (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f')
    (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (hsym : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ)
    (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) :
    Set.Finite {y : grp G β | FixL G v β y z ∧
      f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0} := by
  obtain ⟨D, hD, hAf⟩ := GlobalTheory.T.formGroup_testFunction_support_bounded_denominators p G β x t hx L f hf h.1
  obtain ⟨k, hP⟩ := GlobalTheory.T.p_adic_denominator_bound p G β K' f' hf' h.2
  obtain ⟨K, hK⟩ := GlobalTheory.T.fixed_vector_squared_bound p G hG v hv β hsym hR z hz
  set N : ℕ := D * p ^ k with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)
  set b := Module.finBasis ℚ G.C with hb
  set S : Finset G.C := Finset.univ.image (fun i => ((N : ℚ)⁻¹) • b i) with hS
  let Φ : G.C →+ (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    AddMonoidHom.mk' (fun c w i l => G.psi w c i l) (by intro a c; funext w i l; simp [map_add])
  refine Set.Finite.of_finite_image ?_ ((grp_val_injective G β).injOn)
  refine GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup Φ (fun k e he => GlobalTheory.T.embeddings_real_independent p G k e he) S _ ?_ (Real.sqrt (max K 0 * N)) ?_
  · rintro _ ⟨y, ⟨-, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    show (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ AddSubgroup.closure (S : Set G.C)
    rw [← b.sum_repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; exact_mod_cast (Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)).ne'
    have e : b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i • b i = m • ((N : ℚ)⁻¹ • b i) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hm, mul_comm, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by
      simp only [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact ⟨i, rfl⟩)) m
  · rintro _ ⟨y, ⟨hfix, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hNpos) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
        calc (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = 1 * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := (one_mul _).symm
          _ ≤ ((N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹) * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
            mul_le_mul_of_nonneg_right h2 hs.le
          _ = N := by field_simp
      exact_mod_cast this
    have hsR : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast hs
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    have h1 := hK y hfix w i j
    have h2 : ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ max K 0 * N :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_max_left K 0) hsR.le).trans
        (mul_le_mul_of_nonneg_left hsN (le_max_right K 0)))
    have h3 := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3

end GlobalTheory.FinFix
