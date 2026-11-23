import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_twist_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N c : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N (-c) R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a e : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a e σ y f :=
    fun a e σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hsH, hsn⟩ := hG.s_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  obtain ⟨hqH, hqn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hsH c
  have e1 : (N : ℤ) + N * -1 + c * 0 = 0 := by ring
  have e2 : -(c : ℤ) + N * b + c * 1 = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N (-c) R, f * t ^ N * s ^ c ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH1, hn1⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N (-c) (N * -1) (N * b) f (t ^ N) hfH hpH
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N + N * -1) (-c + N * b) (c * 0) (c * 1) (f * t ^ N) (s ^ c) hH1 hqH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hn1 σ y, hpn σ y, hqn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    have h2 : P.nu 0 1 σ y s ^ c ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (hsn σ y)
    have h3 : P.nu N (-c) σ y f * P.nu (-1) b σ y t ^ N ≤ R :=
      (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
    exact (mul_le_of_le_one_right (mul_nonneg (nu_nonneg _ _ _ _ _) (pow_nonneg (nu_nonneg _ _ _ _ _) _)) h2).trans h3
  have hinj : Set.InjOn (fun f => f * t ^ N * s ^ c) (P.Bl N (-c) R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) (mul_right_cancel₀ (pow_ne_zero c hG.s_ne) h)
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N (-c) R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, Regime P D → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N (-c) (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b s t hG c hR
  obtain ⟨α, β, hαβ⟩ := hR
  have hb : (0 : ℝ) < b := by exact_mod_cast hG.pos
  have hlim := hαβ (3 / b) (by positivity)
  have hsub : Tendsto (fun N : ℕ => b * N) atTop atTop :=
    tendsto_id.const_mul_atTop' hG.pos
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      P.lc 0 ((b * N : ℕ) : ℤ) (Real.exp (3 / b * ((b * N : ℕ) : ℝ))) / ((b * N : ℕ) : ℝ) ^ (D + 1) < C :=
    ⟨_, (hlim.comp hsub).eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C * (b : ℝ) ^ (D + 1), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have e1 : 3 / (b : ℝ) * ((b * N : ℕ) : ℝ) = 3 * N := by push_cast; field_simp
  have e2 : ((b * N : ℕ) : ℤ) = (N : ℤ) * b := by push_cast; ring
  have hpos : (0 : ℝ) < ((b * N : ℕ) : ℝ) ^ (D + 1) := by push_cast; positivity
  rw [e1, e2, div_lt_iff₀ hpos] at hN
  calc P.lc N (-c) (Real.exp (3 * N)) ≤ P.lc 0 ((N : ℤ) * b) (Real.exp (3 * N)) :=
        lc_twist_le_of_good P hG N c _ (GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 0 _ _)
    _ ≤ C * ((b * N : ℕ) : ℝ) ^ (D + 1) := hN.le
    _ = C * (b : ℝ) ^ (D + 1) * (N : ℝ) ^ (D + 1) := by push_cast; ring

end GlobalTheory.HSNef
