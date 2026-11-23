import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscrStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.DiffSize

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_intCast (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ‖((m : ℤ) : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValInt p m : ℤ)) := by
  have e : ((m : ℤ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((m : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_intCast, map_intCast]
  rw [e]
  refine (PadicComplex.norm_extends' (p := p) _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm),
    padicValRat.of_int]
  push_cast; rfl

theorem pow_mem {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) (k : ℕ) :
    x ^ k ∈ I ^ k := by
  induction k with
  | zero => simpa using FractionalIdeal.one_mem_one (R := 𝓞 K) (K := K)
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx

theorem exists_int_mul_pow {F : Type} [Field F] [NumberField F] [IsGalois ℚ F] {y : F}
    (hy : y ∈ latM (1 : Frac F)) : ∃ c : 𝓞 F, (c : F) = (discr F : F) * y ^ Module.finrank ℚ F := by
  have hd : (discr F : F) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have h1 : latM (1 : Frac F) = ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simp [latM]
  rw [h1] at hy
  have h2 := pow_mem hy (Module.finrank ℚ F)
  rw [inv_pow, ← FractionalIdeal.coeIdeal_pow, GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' F, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv] at h2
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_spanSingleton _).1 h2
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, map_intCast] at hc
  rw [← hc]; field_simp

theorem sz_invDiff : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F] (y : F) (i : Emb F), y ∈ latM (1 : Frac F) → Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F) ((i y : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ _ y i hy
  obtain ⟨c, hc⟩ := exists_int_mul_pow hy
  let φ : F →+* ℂ := Complex.ofRealHom.comp i
  have hmem : ∀ x : F, φ x ∈ algebraicClosure ℚ ℂ := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom φ.toRatAlgHom
  let ψ : F →+* algebraicClosure ℚ ℂ := φ.codRestrict (algebraicClosure ℚ ℂ) hmem
  let χ : F →+* ℂ_[l] := lam.comp ψ
  refine ⟨hmem y, ?_⟩
  change ‖χ y‖ ≤ _
  have hd0 : discr F ≠ 0 := discr_ne_zero F
  have hcint : ‖χ (c : F)‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int χ (RingOfIntegers.isIntegral_coe c); exact Subsingleton.elim _ _)
  have hdn : ‖χ (discr F : F)‖ = (l : ℝ) ^ (-(padicValInt l (discr F) : ℤ)) := by
    rw [map_intCast]; exact norm_intCast l _ hd0
  set n := Module.finrank ℚ F
  set v := padicValInt l (discr F)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hkey : ‖χ y‖ ^ n * (l : ℝ) ^ (-(v : ℤ)) ≤ 1 := by
    rw [← hdn, ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, mul_comm, ← hc]; exact hcint
  have hpow : ‖χ y‖ ^ n ≤ (l : ℝ) ^ (v : ℝ) := by
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(v : ℤ)) := zpow_pos hl0 _
    have := (le_div_iff₀ hpos).2 hkey
    rw [one_div, ← zpow_neg, neg_neg, zpow_natCast] at this
    rwa [Real.rpow_natCast]
  have hn : 0 < n := Module.finrank_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ‖χ y‖ = (‖χ y‖ ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne').symm
    _ ≤ ((l : ℝ) ^ (v : ℝ)) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (l : ℝ) ^ ((v : ℝ) / n) := by rw [← Real.rpow_mul hl0.le, div_eq_mul_inv]

end GlobalTheory.DiffSize
