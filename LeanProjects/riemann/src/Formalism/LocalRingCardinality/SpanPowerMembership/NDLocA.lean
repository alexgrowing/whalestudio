import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise

variable (l : ℕ) [hl : Fact l.Prime]

theorem denseRange_emb {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) :
    DenseRange j := by
  have : CharZero Ω := (RingHom.charZero_iff j.injective).mpr inferInstance
  rw [Metric.denseRange_iff]
  intro a ε hε
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set f := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fa0 : aeval a f = 0 := minpoly.aeval _ _
  have hn : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hε' : (ε / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  have hd : DenseRange (algebraMap ℚ ℚ_[l]) := by
    have := Padic.denseRange_ratCast l
    convert this using 1
    funext q
    exact eq_ratCast _ q
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd fmon hε'
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε' fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < ε := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos hε (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have e : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l)) =
      (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, rfl⟩ := hb
  exact ⟨c, by rw [dist_eq_norm]; exact hab⟩

def ball : ValuationSubring (PadicAlgCl l) :=
  (Valued.v : Valuation (PadicAlgCl l) NNReal).valuationSubring

theorem mem_ball (x : PadicAlgCl l) : x ∈ ball l ↔ ‖x‖ ≤ 1 := by
  rw [ball, Valuation.mem_valuationSubring_iff]
  first
    | exact Iff.rfl
    | (rw [← NNReal.coe_le_coe]; rfl)
    | simp

variable {l} {Ω : Type} [Field Ω]

def placeJ (j : Ω →+* PadicAlgCl l) : ValuationSubring Ω := (ball l).comap j

theorem mem_placeJ (j : Ω →+* PadicAlgCl l) (x : Ω) : x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
  rw [placeJ, ValuationSubring.mem_comap, mem_ball]

theorem val_lt_one_iff {A : ValuationSubring Ω} {j : Ω →+* PadicAlgCl l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : A.valuation y < 1 ↔ ‖j y‖ < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  · have hjy : j y ≠ 0 := (map_ne_zero j).2 hy
    have hpos : 0 < ‖j y‖ := norm_pos_iff.2 hjy
    have e1 := (Valuation.one_lt_val_iff A.valuation (inv_ne_zero hy)).symm
    rw [inv_inv] at e1
    rw [e1, ← not_le, ValuationSubring.valuation_le_one_iff, hj, map_inv₀, norm_inv, not_le]
    first
      | exact one_lt_inv₀ hpos
      | (rw [one_lt_inv_iff₀]; simp [hpos])

variable (l) in
theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv.toMulEquiv]
  simpa using h

variable (l) in

def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  rw [show (vQ l).asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} from rfl, Ideal.mem_span_singleton,
    ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp

theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact intCast_mem A n

theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hp : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
    have hc : IsCoprime ((l : ℕ) : ℤ) n := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hnd
    obtain ⟨u, w, huw⟩ := hc
    have h1 : A.valuation ((u : Ω) * ((l : ℕ) : Ω)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (val_intCast_le_one A u)).trans_lt hA
    have h2 : A.valuation ((w : Ω) * (n : Ω)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (val_intCast_le_one A w)).trans_lt h
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    have h4 : ((u : Ω) * ((l : ℕ) : Ω)) + (w : Ω) * (n : Ω) = 1 := by
      have := congrArg (Int.cast (R := Ω)) huw
      push_cast at this
      exact this
    rw [h4, map_one] at h3
    exact lt_irrefl _ h3
  · rintro ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact (mul_le_of_le_one_right' (val_intCast_le_one A m)).trans_lt hA

theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  unfold IsPlaceOver
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ((n : 𝓞 ℚ)) = x :=
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [← eq_intCast Rat.ringOfIntegersEquiv.symm, RingEquiv.symm_apply_apply]⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA n]
  first
    | simp
    | (push_cast; rfl)
    | norm_cast

theorem exists_emb [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    ∃ j : Ω →+* PadicAlgCl l, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let j0 : Ω →ₐ[ℚ] PadicAlgCl l := IsAlgClosed.lift
  have h0 : (placeJ (j0 : Ω →+* PadicAlgCl l)).valuation ((l : ℕ) : Ω) < 1 := by
    rw [val_lt_one_iff (mem_placeJ _), map_natCast]
    have h1 : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖((l : ℕ) : ℚ_[l])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ _ h0) (isPlaceOver_vQ A hA)
  refine ⟨(j0 : Ω →+* PadicAlgCl l).comp ((σ⁻¹ : G ℚ Ω) : Ω →+* Ω), fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_placeJ]
  rfl

end Formalism.BasicNotions.Examples₂.LB
