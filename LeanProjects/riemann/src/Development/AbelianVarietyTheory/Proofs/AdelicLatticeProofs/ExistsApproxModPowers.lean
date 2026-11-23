import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mul_pow_mem_nhds {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    {p : ℕ} (hp : 0 < p) {y : K} (hy : y ≠ 0) :
    {a : K | a ≠ 0 ∧ ∃ r : K, a = y * r ^ p} ∈ nhds y := by
  have hd : HasStrictDerivAt (fun r : K => y * r ^ p) (y * ((p : K) * 1 ^ (p - 1))) 1 :=
    (hasStrictDerivAt_pow p (1 : K)).const_mul y
  have hne : y * ((p : K) * 1 ^ (p - 1)) ≠ 0 := by
    have : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    simp [hy, this]
  have h := hd.map_nhds_eq hne
  simp only [one_pow, mul_one] at h
  refine Filter.inter_mem (isOpen_ne.mem_nhds hy) ?_
  rw [← h]
  exact Filter.mem_map.2 (Filter.Eventually.of_forall fun r => ⟨r, rfl⟩)

theorem exists_approx_mod_powers :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  intro p F _ _ S y hp hy
  let U : Set (((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    ⋂ v : S, {q | q.1 v ≠ 0 ∧ ∃ r : v.1.adicCompletion F, q.1 v = y v.1 * r ^ p}
  have hU : U ∈ nhds ((fun v : S => y v.1), (0 : (F →+* ℝ) → ℝ)) := by
    refine Filter.iInter_mem.2 fun v => ?_
    have hc : Continuous fun q : ((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ) => q.1 v :=
      (continuous_apply v).comp continuous_fst
    have : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    letI : NontriviallyNormedField (v.1.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.1.adicCompletion F) ℤᵐ⁰
    exact hc.continuousAt.preimage_mem_nhds
      (mul_pow_mem_nhds (K := v.1.adicCompletion F) hp (hy v.1))
  obtain ⟨x, hx⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real F S).mem_nhds hU
  have h1 : ∀ v : S, algebraMap F (v.1.adicCompletion F) x ≠ 0 ∧
      ∃ r : v.1.adicCompletion F, algebraMap F (v.1.adicCompletion F) x = y v.1 * r ^ p :=
    fun v => Set.mem_iInter.1 hx v
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨1, one_ne_zero, fun v hv => absurd (map_zero _) (h1 ⟨v, hv⟩).1⟩
  · exact ⟨x, hx0, fun v hv => (h1 ⟨v, hv⟩).2⟩

end GlobalTheory.CNorm
