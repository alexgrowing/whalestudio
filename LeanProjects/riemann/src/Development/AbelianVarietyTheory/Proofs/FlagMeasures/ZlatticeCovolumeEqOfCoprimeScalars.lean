import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.CovScal

theorem abs_det_mul_covolume_eq_nat_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (A B : Submodule ℤ E) [DiscreteTopology A] [IsZLattice ℝ A]
    [DiscreteTopology B] [IsZLattice ℝ B] (T : E →ₗ[ℝ] E) (hT : ∀ y ∈ A, T y ∈ B) :
    ∃ n : ℕ, |LinearMap.det T| * ZLattice.covolume A μ = n * ZLattice.covolume B μ := by
  classical

  let bA := Module.Free.chooseBasis ℤ A
  let bB := Module.Free.chooseBasis ℤ B
  let b₀ := bA.ofZLatticeBasis ℝ A
  let e := (bB.ofZLatticeBasis ℝ B).indexEquiv b₀
  let bB' := bB.reindex e
  let c := bB'.ofZLatticeBasis ℝ B
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ A) (Module.Free.ChooseBasisIndex ℤ A) ℤ :=
    fun i j => bB'.repr ⟨T (bA j), hT _ (bA j).2⟩ i
  have hb₀ : ((↑) : A → E) ∘ bA = b₀ := funext fun i => (bA.ofZLatticeBasis_apply ℝ A i).symm
  have hc : ((↑) : B → E) ∘ bB' = c := funext fun i => (bB'.ofZLatticeBasis_apply ℝ B i).symm

  have hM : c.toMatrix (T ∘ b₀) = M.map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.map_apply, Function.comp_apply,
      show b₀ j = ((bA j : A) : E) from bA.ofZLatticeBasis_apply ℝ A j]
    exact bB'.ofZLatticeBasis_repr_apply ℝ B ⟨T (bA j), hT _ (bA j).2⟩ i
  have hdet : LinearMap.det T = b₀.det c * (M.det : ℝ) := by
    have h1 : b₀.det (T ∘ b₀) = LinearMap.det T := by
      rw [b₀.det_comp T b₀, b₀.det_self, mul_one]
    rw [← h1, b₀.det_apply, ← b₀.toMatrix_mul_toMatrix c (T ∘ b₀), Matrix.det_mul,
      ← b₀.det_apply, hM, Int.cast_det]
  have hcA := ZLattice.covolume_eq_det_mul_measureReal A μ bA b₀
  have hcB := ZLattice.covolume_eq_det_mul_measureReal B μ bB' b₀
  rw [hb₀, b₀.det_self, abs_one, one_mul] at hcA
  rw [hc] at hcB
  refine ⟨M.det.natAbs, ?_⟩
  rw [hcA, hcB, hdet, Nat.cast_natAbs, Int.cast_abs, abs_mul]
  ring

noncomputable def blockScal {ι : Type} (κ : Type) (d : ι → ℝ) : (ι → κ → ℝ) →ₗ[ℝ] (ι → κ → ℝ) :=
  LinearMap.pi fun v => (d v • (LinearMap.id : (κ → ℝ) →ₗ[ℝ] (κ → ℝ))).comp (LinearMap.proj v)

theorem blockScal_apply {ι κ : Type} (d : ι → ℝ) (y : ι → κ → ℝ) :
    blockScal κ d y = fun v i => d v * y v i := by
  funext v i
  simp [blockScal]

theorem det_blockScal {ι κ : Type} [Fintype ι] [Fintype κ] (d : ι → ℝ) :
    LinearMap.det (blockScal κ d) = ∏ v, d v ^ Fintype.card κ := by
  unfold blockScal
  rw [LinearMap.det_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]

theorem eq_one_of_forall_prime {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ p : ℕ, p.Prime → ∃ a b : ℕ, ¬ p ∣ a * b ∧ ρ ^ 2 * b = a) : ρ = 1 := by
  obtain ⟨a₀, b₀, h2, hab₀⟩ := h 2 Nat.prime_two
  have ha₀ : a₀ ≠ 0 := by rintro rfl; simp at h2
  have hb₀ : b₀ ≠ 0 := by rintro rfl; simp at h2

  have key : a₀ = b₀ := by
    refine Nat.eq_of_factorization_eq ha₀ hb₀ fun p => ?_
    by_cases hp : p.Prime
    · obtain ⟨a, b, hp', hab⟩ := h p hp
      have ha : a ≠ 0 := by rintro rfl; simp at hp'
      have hb : b ≠ 0 := by rintro rfl; simp at hp'
      have hcast : ((a₀ * b : ℕ) : ℝ) = ((a * b₀ : ℕ) : ℝ) := by
        push_cast
        rw [← hab₀, ← hab]
        ring
      have hnat : a₀ * b = a * b₀ := by exact_mod_cast hcast
      have hpa : a.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_left hd b)
      have hpb : b.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_right hd a)
      have hf := congrArg (fun n => n.factorization p) hnat
      simp only [Nat.factorization_mul ha₀ hb, Nat.factorization_mul ha hb₀, Finsupp.add_apply,
        hpa, hpb] at hf
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [key] at hab₀
  have hb₀' : (b₀ : ℝ) ≠ 0 := by exact_mod_cast hb₀
  have hsq : ρ ^ 2 = 1 := mul_right_cancel₀ hb₀' (by rw [hab₀, one_mul])
  have hfac : (ρ - 1) * (ρ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h' | h' <;> linarith

theorem covolume_eq_of_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  intro ι κ _ _ A B _ _ _ _ h
  have hA : 0 < ZLattice.covolume A volume := ZLattice.covolume_pos A volume
  have hB : 0 < ZLattice.covolume B volume := ZLattice.covolume_pos B volume
  set cA := ZLattice.covolume A volume
  set cB := ZLattice.covolume B volume
  suffices key : cA / cB = 1 from (div_eq_one_iff_eq hB.ne').mp key
  refine eq_one_of_forall_prime (div_pos hA hB) fun p hp => ?_
  obtain ⟨d, N, hpN, hN, hAB, hBA⟩ := h p hp
  have hT : ∀ y ∈ A, blockScal κ d y ∈ B := fun y hy => by rw [blockScal_apply]; exact hAB y hy
  have hT' : ∀ y ∈ B, blockScal κ d y ∈ A := fun y hy => by rw [blockScal_apply]; exact hBA y hy
  obtain ⟨n, hn⟩ := abs_det_mul_covolume_eq_nat_mul volume A B (blockScal κ d) hT
  obtain ⟨m, hm⟩ := abs_det_mul_covolume_eq_nat_mul volume B A (blockScal κ d) hT'
  set D := |LinearMap.det (blockScal κ d)|

  have hD2 : D ^ 2 = (N : ℝ) ^ Fintype.card κ := by
    rw [sq_abs, det_blockScal, ← hN, Finset.prod_pow, Finset.prod_pow]
    ring
  have hnm : ((n * m : ℕ) : ℝ) = ((N ^ Fintype.card κ : ℕ) : ℝ) := by
    push_cast
    have h0 : ((n : ℝ) * m - D ^ 2) * (cA * cB) = 0 := by
      linear_combination (-(D * cB)) * hn - (n * cB) * hm
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rw [← hD2]; linarith
    · exact absurd h0 (mul_pos hA hB).ne'
  have hnat : n * m = N ^ Fintype.card κ := by exact_mod_cast hnm
  refine ⟨n, m, ?_, ?_⟩
  · rw [hnat]
    exact fun hd => hpN (hp.dvd_of_dvd_pow hd)
  · rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hB.ne')]
    linear_combination (-cA) * hm + cB * hn

end GlobalTheory.CovScal
