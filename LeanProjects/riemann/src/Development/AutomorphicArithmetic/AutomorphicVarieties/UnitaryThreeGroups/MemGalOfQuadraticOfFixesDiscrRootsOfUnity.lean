import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base

private theorem UpperTheory.exists_fixed_square_root_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (g : Ω →+* Ω) (n : ℕ) :
    Odd n → (∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ) →
      ∃ m : ℤ, m.natAbs = n ∧ m % 4 = 1 ∧ ∃ s : Ω, s ^ 2 = m ∧ g s = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hg
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, rfl, rfl, 1, by norm_num, map_one g⟩
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      rw [← hp_def] at hk
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hk
        obtain ⟨a, ha⟩ := hn
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · obtain ⟨a, ha⟩ := hn
          rw [h, mul_zero] at hk
          omega
        · exact h
      have hkn : k < n := by
        rw [hk]
        have := hp.two_le
        nlinarith
      have hkodd : Odd k := (Nat.odd_mul.mp (hk ▸ hn)).2
      obtain ⟨m', hm'abs, hm'4, s', hs'sq, hgs'⟩ :=
        ih k hkn hkodd (fun ζ hζ => hg ζ (by rw [hk, pow_mul', hζ, one_pow]))
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
      obtain ⟨⟨x, hx⟩, hall⟩ := CF.gauss Ω p ζ hp2 hζ
      have hgz : g ζ = ζ ^ 1 := by
        rw [pow_one]
        exact hg ζ (by rw [hk, pow_mul, hζ.pow_eq_one, one_pow])
      have hgx : g x = x := by
        have := (hall x hx).2 g 1 hgz
        simpa [legendreSym.at_one] using this
      have hps : (CF.pStar p).natAbs = p := by
        simp [CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
      have hp4 : CF.pStar p % 4 = 1 := by
        obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
        clear_value p
        rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
        · have e : p / 2 = 2 * c := by omega
          have hpz : (p : ℤ) = 4 * c + 1 := by omega
          rw [CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
        · have e : p / 2 = 2 * c + 1 := by omega
          have hpz : (p : ℤ) = 4 * c + 3 := by omega
          rw [CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
      refine ⟨CF.pStar p * m', ?_, ?_, x * s', ?_, ?_⟩
      · rw [Int.natAbs_mul, hps, hm'abs, hk]
      · rw [Int.mul_emod, hp4, hm'4]
        rfl
      · rw [mul_pow, hx, hs'sq]
        push_cast
        ring
      · rw [map_mul, hgx, hgs']

theorem UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → Odd (discr K).natAbs → ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (discr K).natAbs = 1 → g ζ = ζ) → g ∈ galOf ℚ K Ω := by
  intro Ω _ _ _ K _ _ _ hK hodd g hg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨m, hmabs, hm4, s, hs, hgs⟩ :=
    UpperTheory.exists_fixed_square_root_odd (g : Ω →+* Ω) (discr K).natAbs hodd (fun ζ h => by simpa using hg ζ h)
  have hd4 : discr K % 4 = 1 := by
    have h2 : Odd (discr K) := Int.natAbs_odd.mp hodd
    rcases GlobalTheory.QuadraticZeta.discr_mod_four hK with h | h
    · obtain ⟨c, hc⟩ := h2
      omega
    · exact h
  have hm : m = discr K := by
    rcases Int.natAbs_eq_natAbs_iff.mp hmabs with h | h
    · exact h
    · rw [h] at hm4
      omega
  subst hm
  have hgs' : g s = s := by simpa using hgs
  obtain ⟨b, t, n, hb0, hb1, hd⟩ := GlobalTheory.QuadraticZeta.exists_basis hK
  set θ : Ω := algebraMap K Ω ((b 1 : 𝓞 K) : K) with hθ
  have hθ2 : θ ^ 2 = t * θ - n := by
    have := congrArg (fun z : 𝓞 K => algebraMap K Ω (z : K)) hb1
    simpa [hθ] using this
  have hy : (2 * θ - t) ^ 2 = s ^ 2 := by
    rw [hs, hd]
    push_cast
    linear_combination 4 * hθ2
  have hgθ : g θ = θ := by
    have hgy : g (2 * θ - t) = 2 * θ - t := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
      · rw [h, hgs']
      · rw [h, map_neg, hgs']
    have e : 2 * g θ - t = 2 * θ - t := by
      rw [← hgy, map_sub, map_mul, map_ofNat, map_intCast]
    linear_combination (1 / 2 : Ω) * e
  have hint : ∀ a : 𝓞 K, g (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K) := by
    intro a
    have e : algebraMap K Ω (a : K) = ((b.repr a 0 : ℤ) : Ω) + ((b.repr a 1 : ℤ) : Ω) * θ := by
      conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b hb0 a]
      simp [hθ]
    rw [e, map_add, map_mul, map_intCast, map_intCast, hgθ]
  change ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x
  intro x
  obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  rw [map_div₀, map_div₀]
  exact congrArg₂ (· / ·) (hint a) (hint c)
