import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrderStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocalStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.PeriodFormPos

open Matrix in

theorem real_pos_of_int_pos {ι : Type} [Fintype ι] (M : ι → ι → ℤ) (hs : ∀ i k, M i k = M k i)
    (hM : ∀ z : ι → ℤ, z ≠ 0 → 0 < ∑ i, ∑ k, z i * z k * M i k) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ k, x i * x k * (M i k : ℝ) := by
  classical
  have hM0 : ∀ z : ι → ℤ, 0 ≤ ∑ i, ∑ k, z i * z k * M i k := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · exact (hM z hz).le
  have hQ : ∀ q : ι → ℚ, (0 : ℝ) ≤ ∑ i, ∑ k, (q i : ℝ) * (q k : ℝ) * (M i k : ℝ) := by
    intro q
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
    choose z hz using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero d.2
    have hz' : ∀ i, (z i : ℝ) = ((d : ℤ) : ℝ) * (q i : ℝ) := by
      intro i
      have h := hz i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at h
      have := congrArg (fun t : ℚ => (t : ℝ)) h
      simpa using this
    have h1 : (0 : ℝ) ≤ ∑ i, ∑ k, (z i : ℝ) * (z k : ℝ) * (M i k : ℝ) := by exact_mod_cast hM0 z
    have h2 : ∑ i, ∑ k, (z i : ℝ) * (z k : ℝ) * (M i k : ℝ) =
        ((d : ℤ) : ℝ) ^ 2 * ∑ i, ∑ k, (q i : ℝ) * (q k : ℝ) * (M i k : ℝ) := by
      simp only [Finset.mul_sum, hz']
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [h2] at h1
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h1
  have hR : ∀ y : ι → ℝ, (0 : ℝ) ≤ ∑ i, ∑ k, y i * y k * (M i k : ℝ) := by
    intro y
    have hdr : DenseRange (Pi.map (fun (_ : ι) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hdr.induction_on y (isClosed_le continuous_const (by fun_prop)) ?_
    intro q
    exact hQ q
  have hform : ∀ y : ι → ℝ, star y ⬝ᵥ ((Matrix.of M).map (Int.cast : ℤ → ℝ)) *ᵥ y =
      ∑ i, ∑ k, y i * y k * (M i k : ℝ) := by
    intro y
    simp only [dotProduct, mulVec, Finset.mul_sum, star_trivial, map_apply, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hpsd : ((Matrix.of M).map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun y => by rw [hform]; exact hR y⟩
    ext i k
    simp [hs i k]
  have hdet : (Matrix.of M).det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hM v hv
    have h2 : ∑ i, ∑ k, v i * v k * M i k = v ⬝ᵥ (Matrix.of M) *ᵥ v := by
      simp only [dotProduct, mulVec, Finset.mul_sum, of_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [h2, hv0] at h1
    simp at h1
  have hpd : ((Matrix.of M).map (Int.cast : ℤ → ℝ)).PosDef := by
    refine hpsd.posDef_iff_det_ne_zero.2 ?_
    have := (Int.castRingHom ℝ).map_det (Matrix.of M)
    rw [RingHom.mapMatrix_apply] at this
    simp only [Int.coe_castRingHom, eq_intCast] at this
    rw [← this]
    exact_mod_cast hdet
  rw [← hform]
  exact hpd.dotProduct_mulVec_pos hx

theorem real_pos_of_discrete {X ι : Type} [AddCommGroup X] [Fintype ι] (b : Module.Basis ι ℤ X)
    (β : X → X → ℝ) (hs : ∀ a a', β a a' = β a' a)
    (hadd : ∀ a a' y, β (a + a') y = β a y + β a' y) (c : ℝ) (hc : 0 < c)
    (hint : ∀ a a', ∃ n : ℤ, β a a' = c * n) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (x : ι → ℝ) (hx : x ≠ 0) : 0 < ∑ i, ∑ k, x i * x k * β (b i) (b k) := by
  choose n hn using hint
  have hsum : ∀ (z : ι → ℤ) (y : X), β (∑ i, z i • b i) y = ∑ i, (z i : ℝ) * β (b i) y := by
    intro z y
    have := map_sum (AddMonoidHom.mk' (fun a => β a y) (fun a a' => hadd a a' y))
      (fun i => z i • b i) Finset.univ
    simp only [map_zsmul, AddMonoidHom.mk'_apply, zsmul_eq_mul] at this
    exact this
  have key := real_pos_of_int_pos (fun i k => n (b i) (b k)) (fun i k => by
      have h := hs (b i) (b k)
      rw [hn, hn] at h
      exact_mod_cast mul_left_cancel₀ hc.ne' h) (fun z hz => by
      have hne : ∑ i, z i • b i ≠ 0 := fun h =>
        hz (funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h))
      have h := hpos _ hne
      rw [hsum] at h
      have h2 : ∑ i, (z i : ℝ) * β (b i) (∑ k, z k • b k) =
          c * ((∑ i, ∑ k, z i * z k * n (b i) (b k) : ℤ) : ℝ) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hs, hsum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hs, hn]
        ring
      rw [h2] at h
      exact_mod_cast (mul_pos_iff_of_pos_left hc).1 h) x hx
  have h3 : ∑ i, ∑ k, x i * x k * β (b i) (b k) =
      c * ∑ i, ∑ k, x i * x k * (n (b i) (b k) : ℝ) := by
    simp only [Finset.mul_sum, hn]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h3]
  exact mul_pos hc key

theorem betaAt_pos : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] [IsDiscreteValuationRing R] (Dg : DegData R (maximalIdeal R)) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), 1 < p → (∀ a ∈ maximalIdeal R, ‖f a‖ < 1) → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord Dg.toPre χ r → f r ≠ 0) → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Dg.toPre.X), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * betaAt Dg.toPre f p (b i) (b k) := by
  intro R _ _ _ _ _ Dg C _ _ f p hp hm hle hne
  have hic : IsIntegrallyClosed R := inferInstance
  obtain ⟨hadd, hsq⟩ := GlobalTheory.T.betaAt_add_left_and_diag_eq_two_order R Dg C f p hic hle hne
  have hco := GlobalTheory.T.psiCoord_exists_unique_up_to_unit_local R Dg hic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hunit : ∀ u : Rˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul]; simp
    have h2 := hle (u⁻¹ : Rˣ)
    have h3 := hle u
    nlinarith [norm_nonneg (f u), norm_nonneg (f (u⁻¹ : Rˣ))]
  have hv : ∀ χ, ∃ r, PsiCoord Dg.toPre χ r ∧ vPsiAt Dg.toPre f p χ = -Real.logb p ‖f r‖ := by
    intro χ
    obtain ⟨r, hr, -⟩ := (hco χ).1
    have h : ∃ r, PsiCoord Dg.toPre χ r := ⟨r, hr⟩
    exact ⟨h.choose, h.choose_spec, by simp only [vPsiAt, dif_pos h]⟩
  have hvn : ∀ χ, ∃ n : ℕ, vPsiAt Dg.toPre f p χ = (-Real.logb p ‖f ϖ‖) * n := by
    intro χ
    obtain ⟨r, hr, hvr⟩ := hv χ
    have hr0 : r ≠ 0 := fun h => hne χ r hr (by rw [h, map_zero])
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
    refine ⟨n, ?_⟩
    rw [hvr, hu, map_mul, norm_mul, hunit, one_mul, map_pow, norm_pow, Real.logb_pow]
    ring
  have hvpos : ∀ χ, χ ≠ 0 → 0 < vPsiAt Dg.toPre f p χ := by
    intro χ hχ
    obtain ⟨r, hr, hvr⟩ := hv χ
    obtain ⟨r₀, hr₀, -, hmem, -⟩ := (hco χ).1
    obtain ⟨u, hu⟩ := (hco χ).2.1 r₀ r hr₀ hr
    have hrm : r ∈ maximalIdeal R := hu ▸ Ideal.mul_mem_left _ _ (hmem hχ)
    rw [hvr, neg_pos]
    exact Real.logb_neg hp' (norm_pos_iff.2 (hne χ r hr)) (hm r hrm)
  refine ⟨Module.Free.ChooseBasisIndex ℤ Dg.toPre.X, inferInstance,
    Module.Free.chooseBasis ℤ Dg.toPre.X, fun x hx => ?_⟩
  obtain ⟨i, -⟩ := Function.ne_iff.1 hx
  have hc : 0 < -Real.logb p ‖f ϖ‖ := by
    obtain ⟨n, hn⟩ := hvn (Module.Free.chooseBasis ℤ Dg.toPre.X i)
    have h := hvpos _ ((Module.Free.chooseBasis ℤ Dg.toPre.X).ne_zero i)
    rw [hn] at h
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (Nat.cast_nonneg (α := ℝ) n)
    linarith
  refine real_pos_of_discrete _ _ (betaAt_symm Dg.toPre f p) hadd _ hc (fun a a' => ?_)
    (fun a ha => ?_) x hx
  · obtain ⟨n₁, h₁⟩ := hvn (a + a')
    obtain ⟨n₂, h₂⟩ := hvn a
    obtain ⟨n₃, h₃⟩ := hvn a'
    refine ⟨(n₁ : ℤ) - n₂ - n₃, ?_⟩
    rw [betaAt, h₁, h₂, h₃]
    push_cast
    ring
  · rw [hsq]
    exact mul_pos two_pos (hvpos a ha)

end GlobalTheory.PeriodFormPos
