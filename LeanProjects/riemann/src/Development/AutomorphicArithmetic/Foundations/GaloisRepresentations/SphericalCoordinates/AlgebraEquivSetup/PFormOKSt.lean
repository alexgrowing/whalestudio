import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem trace_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private theorem hd_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    A.bar (A.hd n i) = A.hd n i := by
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [A.c_real]

private theorem hd_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [this]

private theorem delta_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) : A.δ ≠ 0 := by
  intro h
  have := A.δ_sign A.τ₀ rfl
  simp [h] at this

private theorem alternatingMap_sub_base_eq_alternating_sum_removeNth {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (x : Fin n → 𝓞 E) : A.EF n x x = 0 := by
  rw [Arith.EF_apply]
  set s : 𝓞 E := ∑ i, A.hd n i * x i * A.bar (x i) with hs
  have hbs : A.bar s = s := by
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hd_bar, A.bar_bar]
    ring
  have hc : IsCMField.complexConj E ((s : 𝓞 E) : E) = (s : E) := by
    rw [← A.bar_eq, hbs]
  have h1 : Algebra.trace ℚ E (A.δ * (s : E)) = - Algebra.trace ℚ E (A.δ * (s : E)) := by
    conv_lhs => rw [← trace_cj, map_mul, A.δ_im, hc, neg_mul, map_neg]
  have h2 : ((A.trd s : ℤ) : ℚ) = 0 := by
    rw [A.trd_spec]
    linarith
  exact_mod_cast h2

private theorem laurent_adjoin_eq_of_image_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    Function.Injective (A.EF n) := by
  refine (injective_iff_map_eq_zero (A.EF n)).2 fun x hx => ?_
  funext i
  by_contra hne
  have hxi : ((x i : 𝓞 E) : E) ≠ 0 := by
    intro h
    exact hne (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hw : A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (delta_ne A) (hd_ne A n i)) hxi
  have hint : ∀ b : 𝓞 E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * (b : E)) = 0 := by
    intro b
    have h0 : A.EF n x (Pi.single i (A.bar b)) = 0 := by rw [hx]; rfl
    rw [Arith.EF_apply] at h0
    have h1 : (∑ j, A.hd n j * x j * A.bar ((Pi.single i (A.bar b) : Fin n → 𝓞 E) j)) =
        A.hd n i * x i * b := by
      rw [Finset.sum_eq_single i]
      · simp [A.bar_bar]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at h0
    have h2 := A.trd_spec (A.hd n i * x i * b)
    rw [h0] at h2
    simp only [Int.cast_zero] at h2
    rw [h2]
    congr 1
    push_cast
    ring
  obtain ⟨b, hb⟩ : ∃ b : E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * b) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hw ((traceForm_nondegenerate ℚ E).1 _ fun b => by simpa [Algebra.traceForm_apply] using hall b)
  obtain ⟨m, hm, hy⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic b))
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 E, (c : E) = (m : ℚ) • b := by
    refine ⟨⟨m • b, hy⟩, ?_⟩
    show m • b = (m : ℚ) • b
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp
  have h3 := hint c
  rw [hc, mul_smul_comm, map_smul, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h5 | h5
  · exact hm (by exact_mod_cast h5)
  · exact hb h5

theorem UpperTheory.Gal.W2.Seed.pFormOKSt :
    FormOKSt := by
  intro E _ _ _ A n
  refine ⟨alternatingMap_sub_base_eq_alternating_sum_removeNth A n, laurent_adjoin_eq_of_image_eq A n, fun b x y => ?_⟩
  rw [Arith.EF_apply, Arith.EF_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, A.bar_bar]
  ring
