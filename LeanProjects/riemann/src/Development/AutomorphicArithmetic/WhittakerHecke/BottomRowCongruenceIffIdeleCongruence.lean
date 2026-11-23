import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.bottomRow_congruence_iff_idele_congruence :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ ζ : (A ℚ)ˣ, ζ ∈ UU → (∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1)) → ∀ y : (A ℚ)ˣ, (∀ v, Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N hN k hk hS ζ hζ hz y
  have hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN1 : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v =>
    show (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ from natCast_mem _ N
  have hv : ∀ v : H.P ℚ, (Bad N v → Valued.v (N : H.Kv v) < 1) ∧ (¬ Bad N v → Valued.v (N : H.Kv v) = 1) := fun v => by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (N : 𝓞 ℚ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    have h2 : Valued.v (N : H.Kv v) = v.intValuation (N : 𝓞 ℚ) := by simpa using h1
    rw [h2]
    exact ⟨fun h => (v.intValuation_lt_one_iff_mem _).2 h, fun h => HeightOneSpectrum.intValuation_eq_one_iff.2 h⟩
  have key : ∀ v : H.P ℚ, (Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔
      ((Bad N v → Dv N v ((y : A ℚ) - 1)) ∧ Valued.v (H.cp v (y : A ℚ)) ≤ 1) := fun v => by
    have hd : H.cp v (k 0 0) * H.cp v (k 1 1) - H.cp v (k 0 1) * H.cp v (k 1 0) = 1 := by
      have := congrArg (H.cp v) ((Matrix.det_fin_two k.1).symm.trans k.2)
      simpa using this
    have hs := hS v
    have hz' := hz v
    have hu := hζ.2 v
    have i00 := hi v 0 0
    have i01 := hi v 0 1
    have i10 := hi v 1 0
    have i11 := hi v 1 1
    simp only [Dv, map_mul, map_sub, map_one] at hs hz' ⊢
    generalize H.cp v (k 0 0) = a at *
    generalize H.cp v (k 0 1) = b at *
    generalize H.cp v (k 1 0) = c at *
    generalize H.cp v (k 1 1) = d at *
    generalize H.cp v (y : A ℚ) = x at *
    generalize H.cp v (ζ : A ℚ) = z at *
    by_cases hb : Bad N v
    · have h1 := hz'.1 hb
      have hlt := (hv v).1 hb
      have h2 : Valued.v (z * d) = 1 := by
        have := Valuation.map_one_add_of_lt Valued.v (h1.trans_lt hlt)
        rwa [add_sub_cancel] at this
      constructor
      · rintro ⟨-, h3⟩
        have h4 : Valued.v x ≤ 1 := by
          have := Valuation.map_one_add_of_lt Valued.v (h3.trans_lt hlt)
          rw [add_sub_cancel, mul_assoc, map_mul, h2, mul_one] at this
          exact this.le
        refine ⟨fun _ => ?_, h4⟩
        rw [show x - 1 = (x * z * d - 1) - x * (z * d - 1) by ring]
        exact Valuation.map_sub_le _ h3 (by rw [map_mul]; exact (mul_le_mul' h4 h1).trans_eq (one_mul _))
      · rintro ⟨h3, h4⟩
        refine ⟨by rw [hu, mul_one]; exact (mul_le_mul' h4 hs).trans_eq (one_mul _), ?_⟩
        rw [show x * z * d - 1 = (x - 1) * (z * d) + (z * d - 1) by ring]
        exact Valuation.map_add_le _ (by rw [map_mul, h2, mul_one]; exact h3 hb) h1
    · obtain rfl := hz'.2 hb
      rw [(hv v).2 hb]
      simp only [map_one, mul_one]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨fun h => absurd h hb, ?_⟩
        rw [show x = a * ((x * d - 1) + 1) - b * (x * c) by linear_combination (-x) * hd]
        refine Valuation.map_sub_le _ ?_ ?_
        · rw [map_mul]
          exact mul_le_one' i00 (Valuation.map_add_le _ h4 (map_one _).le)
        · rw [map_mul, map_mul]
          exact mul_le_one' i01 h3
      · rintro ⟨-, h4⟩
        exact ⟨mul_le_one' h4 i10, Valuation.map_sub_le _ (by rw [map_mul]; exact mul_le_one' h4 i11) (map_one _).le⟩
  simp only [key, forall_and]
