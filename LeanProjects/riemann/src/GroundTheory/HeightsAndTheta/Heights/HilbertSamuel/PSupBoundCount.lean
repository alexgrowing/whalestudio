import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix

noncomputable section

namespace SupBoundCount

theorem main {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ f : MRing ι, IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f)
    {r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ} (hb : IsSecBasisM d.y d.k₀ n b) :
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      -(1 / 2) * Real.log (blockGram d n b).det - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n := by
  classical
  rw [finrank_secM hb]
  have hb' := hb
  choose f hf hbf using hb.1
  have hbe : b = fun j => map (Int.castRingHom ℚ) (f j) := funext hbf
  subst hbe
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb'.2.1
    simpa [aeval_map_int] using this
  have hG := gram_posDef d n f hf hli hc hsup
  refine ⟨rank_le d n f hf hli hc hsup, ?_⟩

  set Q : (Fin r → ℤ) → ℝ := fun m => (fun k => (m k : ℝ)) ⬝ᵥ
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)) with hQ
  set P : (Fin r → ℤ) → Prop := fun m =>
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y (∑ k, m k • f k)) with hPdef
  have hP1 : ∀ m, Q m ≤ (1 / c) ^ 2 → P m := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    refine (isSmallH_iff d n hF).2 fun z hz => ?_
    have h1 := hsup _ hF z hz
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    have h2 : Real.sqrt (Q m) ≤ 1 / c := by
      calc Real.sqrt (Q m) ≤ Real.sqrt ((1 / c) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / c := Real.sqrt_sq (by positivity)
    have h3 : c * Real.sqrt (Q m) ≤ 1 := by
      calc c * Real.sqrt (Q m) ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h2 hc.le
        _ = 1 := by field_simp
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    exact (div_le_one hp).1 (h1.trans h3)
  have hP2 : ∀ m, P m → Q m ≤ 1 := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    have h1 := blockL2Norm_le_one_of_sup_bound d n hF ((isSmallH_iff d n hF).1 hm)
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    by_contra h
    push_neg at h
    have := Real.sqrt_lt_sqrt zero_le_one h
    rw [Real.sqrt_one] at this
    linarith
  obtain ⟨-, hcount⟩ := count_of_gram hG (by positivity : (0 : ℝ) < 1 / c) P hP1 hP2

  have hmem : ∀ m : Fin r → ℤ, aeval d.y (∑ k, m k • f k) ∈ secM d.y (blockDeg d.k₀ n) := by
    intro m
    rw [← hb'.2.2]
    simp only [map_sum, map_zsmul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, by simp [aeval_map_int]⟩)
  have hinj : Function.Injective fun m : Fin r → ℤ => aeval d.y (∑ k, m k • f k) := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • aeval d.y (f k) = 0 := by
      simp only [map_sum, map_zsmul] at h
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)
  let E : {m // P m} → {s : secM d.y (blockDeg d.k₀ n) // IsSmallH (mCoordIdeal d.y) d.y d.A n (s : Ω)} :=
    fun m => ⟨⟨_, hmem m.1⟩, m.2⟩
  have hE : Function.Bijective E := by
    refine ⟨fun m m' h => Subtype.ext (hinj (congrArg (fun s => ((s.1 : secM d.y _) : Ω)) h)), ?_⟩
    rintro ⟨⟨s, hs⟩, hsm⟩
    have hs' := hs
    rw [← hb'.2.2] at hs'
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hs'
    have hms : aeval d.y (∑ k, m k • f k) = s := by
      rw [← hm]
      simp [map_sum, aeval_map_int]
    refine ⟨⟨m, ?_⟩, ?_⟩
    · show IsSmallH _ _ _ _ _
      rw [hms]
      exact hsm
    · exact Subtype.ext (Subtype.ext hms)
  have hcard := Nat.card_congr (Equiv.ofBijective E hE)
  simp only [smallSectionCount]
  rw [← hcard]

  have hV : (r : ℝ) * Real.log (2 / Real.sqrt r) ≤ Real.log (unitBallVolume r) := by
    have hpos : 0 < (2 / Real.sqrt r) ^ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · exact pow_pos (div_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast h0))) r
    rw [← Real.log_pow]
    exact Real.log_le_log hpos (MinkowskiCount.cube_le_unitBallVolume r)
  have halg : (r : ℝ) * Real.log (2 / Real.sqrt r) + r * Real.log (1 / c / 2) =
      -((r : ℝ) * Real.log (c * Real.sqrt r)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast h0)
      rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
      have : 2 / Real.sqrt r * (1 / c / 2) = (c * Real.sqrt r)⁻¹ := by
        field_simp
      rw [this, Real.log_inv]
      ring
  linarith

end SupBoundCount

theorem SupBoundCount.proof : SupBoundCount.Statement := by
  intro D K _ _ ι _ Ω _ _ d n c hc hsup
  have hex := SupBoundCount.exists_isSecBasisM d.y d.k₀ n
  have h := SupBoundCount.main d n hc hsup hex.choose_spec
  refine ⟨h.1, ?_⟩
  rw [blockChi, dif_pos hex]
  exact h.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
