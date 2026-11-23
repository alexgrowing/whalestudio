import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

open Polynomial in
private theorem sqrt_div_mul_eq_sqrt_mul (p : ℕ) (L : Type) [Field L] [Algebra ℚ L]
    [h : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : ∃ s : L, s ^ 2 = -(p : L) := by
  have hs := h.splits
  have hd : ((X ^ 2 + C (p : ℚ) : ℚ[X]).map (algebraMap ℚ L)).degree ≠ 0 := by
    rw [degree_map, degree_X_pow_add_C two_pos]
    norm_num
  obtain ⟨s, hs⟩ := hs.exists_eval_eq_zero hd
  refine ⟨s, eq_neg_of_add_eq_zero_left ?_⟩
  simpa using hs

open Polynomial in
private theorem sqrt_kstar (p : ℕ) : ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  exact @sqrt_div_mul_eq_sqrt_mul p (SplittingField (X ^ 2 + C (p : ℚ) : ℚ[X])) _ _
    (Polynomial.IsSplittingField.splittingField _)

theorem UpperTheory.V.HV.kstarRam :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra (Kstar p) Ω] (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
      ¬ Ine (F := ℚ) A ≤ galOf ℚ (Kstar p) Ω := by
  intro p hp hp4 Ω _ _ _ _ A hA hle
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  have hsub : Subsingleton (ZMod (ordCompl[p] p))ˣ := by
    have hd : ordCompl[p] p = 1 := by
      rw [Nat.Prime.factorization_self hp, pow_one, Nat.div_self hp.pos]
    rw [hd]
    infer_instance
  have hmem : (-1 : (ZMod p)ˣ) ∈ UpperTheory.V.B3.pPart p p := by
    unfold UpperTheory.V.B3.pPart
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [← UpperTheory.V.B1.cycIne Ω p p A hA] at hmem
  obtain ⟨g, hg, hgb⟩ := hmem
  haveI : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  obtain ⟨s0, hs0⟩ := sqrt_kstar p
  set s : Ω := algebraMap (Kstar p) Ω s0 with hsdef
  have hodd : Odd (p / 2) := Nat.odd_iff.mpr (by omega)
  have hs : s ^ 2 = ((UpperTheory.V.CF.pStar p : ℤ) : Ω) := by
    unfold UpperTheory.V.CF.pStar
    push_cast
    rw [Odd.neg_one_pow hodd, hsdef, ← map_pow, hs0]
    simp
  have hgauss := ((UpperTheory.V.CF.gauss Ω p ζ hp2 hζ).2 s hs).2
  have hgζ := ((UpperTheory.V.B1.cycN_eq_iff ℚ Ω p g (-1)).mp hgb) ζ hζ.pow_eq_one
  have h1 := hgauss (g : Ω →+* Ω) _ hgζ
  have hleg : legendreSym p (((((-1 : (ZMod p)ˣ) : ZMod p).val : ℕ) : ℤ)) = -1 := by
    rw [legendreSym.mod]
    have : ((((-1 : (ZMod p)ˣ) : ZMod p).val : ℕ) : ℤ) % p = (-1 : ℤ) % p := by
      rw [← ZMod.intCast_eq_intCast_iff']
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [this, ← legendreSym.mod, legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp4]
  rw [hleg] at h1
  have hfix : g s = s := hle hg s0
  have h2 : (g : Ω →+* Ω) s = g s := rfl
  rw [h2, hfix] at h1
  have hs_zero : s = 0 := by
    have : (2 : Ω) * s = 0 := by push_cast at h1; linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    · exact h
  have : ((UpperTheory.V.CF.pStar p : ℤ) : Ω) = 0 := by rw [← hs, hs_zero]; ring
  unfold UpperTheory.V.CF.pStar at this
  push_cast at this
  rw [Odd.neg_one_pow hodd] at this
  have : (p : Ω) = 0 := by linear_combination -this
  exact hp.ne_zero (by exact_mod_cast this)
