import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.SizeRat

theorem norm_ratCast (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = (padicNorm l q : ℝ) := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]

theorem sz_ratCast (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) (r : ℝ)
    (hr : -(padicValRat l q : ℝ) ≤ r) : Sz l lam r (q : ℂ) := by
  have hmem : (q : ℂ) ∈ algebraicClosure ℚ ℂ := SubfieldClass.ratCast_mem _ q
  refine ⟨hmem, ?_⟩
  have e : (⟨(q : ℂ), hmem⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
    apply Subtype.ext; simp
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  rw [e, map_ratCast, norm_ratCast]
  by_cases hq : q = 0
  · subst hq; simp only [padicNorm.zero, Rat.cast_zero]; exact Real.rpow_nonneg (by linarith) r
  · rw [padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (by push_cast; exact hr)

theorem sz_exp (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) := by
  set ζ := Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ)) with hζ
  have hpow : ζ ^ q.den = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (q.den : ℂ) * ((2 * Real.pi * Complex.I) * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hq : (q : ℂ) = (q.num : ℂ) / (q.den : ℂ) := by exact_mod_cast (Rat.num_div_den q).symm
      have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
      rw [hq]; field_simp
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I q.num
  have hmem : ζ ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow q.den_pos (by rw [hpow]; exact isIntegral_one)).isAlgebraic
  refine ⟨hmem, ?_⟩
  have h1 : (⟨ζ, hmem⟩ : algebraicClosure ℚ ℂ) ^ q.den = 1 := by
    apply Subtype.ext; simp [hpow]
  have h2 : ‖lam ⟨ζ, hmem⟩‖ ^ q.den = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  have h3 : ‖lam ⟨ζ, hmem⟩‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) q.den_nz).mp h2
  rw [h3, Real.rpow_zero]

theorem sz_rat_exp : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    (∀ (q : ℚ) (r : ℝ), (-(padicValRat l q : ℝ) ≤ r) → Sz l lam r (q : ℂ)) ∧
      ∀ q : ℚ, Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) :=
  fun l _ lam => ⟨sz_ratCast l lam, sz_exp l lam⟩

end GlobalTheory.SizeRat
