import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.places :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
      (A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v) ∧ (A = ⊤ → Ine (F := k) A = ⊥ ∧ ¬ A.valuation (l : Ω) < 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 k), IsPlaceOver A v → (A.valuation (l : Ω) < 1 ↔ v ∈ Above k l)) ∧
      (¬ A.valuation (l : Ω) < 1 → Ine (F := k) A ≤ (cycZ k Ω l).ker) := by
  intro k Ω _ _ _ _ _ l _ A
  have hint : ∀ z : Ω, IsIntegral ℤ z → A.valuation z ≤ 1 := by
    intro z hz
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp (hz.tower_top (A := A))
    exact A.valuation_le_one y
  have hOk : ∀ x : 𝓞 k, A.valuation (algebraMap k Ω (x : k)) ≤ 1 := fun x =>
    hint _ x.isIntegral_coe.algebraMap
  have hl1 : A.valuation (l : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A l)
  have htop : A = ⊤ → ∀ y : Ω, A.valuation y < 1 → y = 0 := by
    intro hA y hy
    by_contra h0
    have h2 : A.valuation y⁻¹ ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _)
    have h3 : A.valuation y * A.valuation y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    have h4 : A.valuation y * A.valuation y⁻¹ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hy
    exact absurd h3 (ne_of_lt h4)
  have hlne : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hA
    let p : Ideal (𝓞 k) :=
      { carrier := {x | A.valuation (algebraMap k Ω (x : k)) < 1}
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_add] at *
          exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
        zero_mem' := by simp
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hOk c)) hx }
    have hprime : p.IsPrime := by
      refine ⟨?_, ?_⟩
      · rw [Ne, Ideal.eq_top_iff_one]
        show ¬ A.valuation (algebraMap k Ω ((1 : 𝓞 k) : k)) < 1
        simp
      · intro x y hxy
        change A.valuation (algebraMap k Ω ((x * y : 𝓞 k) : k)) < 1 at hxy
        change A.valuation (algebraMap k Ω (x : k)) < 1 ∨ A.valuation (algebraMap k Ω (y : k)) < 1
        simp only [map_mul] at hxy
        by_contra h
        push_neg at h
        have hx1 : A.valuation (algebraMap k Ω (x : k)) = 1 := le_antisymm (hOk x) h.1
        have hy1 : A.valuation (algebraMap k Ω (y : k)) = 1 := le_antisymm (hOk y) h.2
        rw [hx1, hy1, one_mul] at hxy
        exact lt_irrefl _ hxy
    have hne : p ≠ ⊥ := by
      intro hbot
      apply hA
      have hk : ∀ y : k, A.valuation (algebraMap k Ω y) ≤ 1 := by
        intro y
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 k) y
        have hb0 : (b : 𝓞 k) ≠ 0 := nonZeroDivisors.ne_zero hb
        have hbv : A.valuation (algebraMap k Ω (algebraMap (𝓞 k) k b)) = 1 := by
          refine le_antisymm (hOk b) (not_lt.mp fun h => hb0 ?_)
          have hbp : b ∈ p := h
          rw [hbot] at hbp
          exact (Submodule.mem_bot _).mp hbp
        rw [map_div₀, map_div₀, hbv, div_one]
        exact hOk a
      have hf : ∀ y : k, algebraMap k Ω y ∈ A := fun y => (A.valuation_le_one_iff _).mp (hk y)
      let f : k →+* A := (algebraMap k Ω).codRestrict A hf
      have hcomp : (algebraMap A Ω).comp f = algebraMap k Ω := by
        ext y
        rfl
      rw [eq_top_iff]
      intro z _
      have hz : IsIntegral A z := by
        obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := k) z
        refine ⟨q.map f, hqm.map f, ?_⟩
        rw [Polynomial.eval₂_map, hcomp]
        exact hq
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hz
      exact y.2
    exact ⟨⟨p, hprime, hne⟩, fun x => Iff.rfl⟩
  · intro hA
    refine ⟨?_, fun h => hlne (htop hA _ h)⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨-, hσ⟩ := hσ
    ext z
    have h1 := hσ z ((A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _))
    have h2 := htop hA _ h1
    rw [sub_eq_zero] at h2
    simpa using h2
  · intro v hv
    have h := hv (l : 𝓞 k)
    simp only [map_natCast] at h
    exact h
  · intro hl σ hσ
    obtain ⟨-, hσ⟩ := hσ
    have hl1' : A.valuation (l : Ω) = 1 := le_antisymm hl1 (not_lt.mp hl)
    have hfix : ∀ (n : ℕ) (t : Ω), t ^ (l ^ n) = 1 → σ t = t := by
      intro n t ht
      have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
      set N := l ^ n with hNdef
      have htI : IsIntegral ℤ t := IsIntegral.of_pow hN (by rw [ht]; exact isIntegral_one)
      have huN : (σ t) ^ N = 1 := by rw [← map_pow, ht, map_one]
      have huI : IsIntegral ℤ (σ t) := IsIntegral.of_pow hN (by rw [huN]; exact isIntegral_one)
      by_contra hne
      set u := σ t with hu
      set s := t ^ (N - 1) with hs
      have hst : s * t = 1 := by rw [hs, ← pow_succ, Nat.sub_add_cancel hN, ht]
      set w := u * s with hw
      have hwN : w ^ N = 1 := by
        rw [hw, mul_pow, huN, one_mul, hs, ← pow_mul, mul_comm (N - 1) N, pow_mul, ht, one_pow]
      have hw1 : w ≠ 1 := by
        intro h
        apply hne
        have h' : w * t = t := by rw [h, one_mul]
        rw [hw, mul_assoc, hst, mul_one] at h'
        exact h'
      have hsI : IsIntegral ℤ s := htI.pow _
      have hwI : IsIntegral ℤ w := huI.mul hsI
      have hval : A.valuation (w - 1) < 1 := by
        have hws : w - 1 = (u - t) * s := by rw [hw, sub_mul, mul_comm t s, hst]
        rw [hws, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint s hsI)) (hσ t (hint t htI))
      set c := ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, w ^ i with hc
      have hcI : IsIntegral ℤ c :=
        IsIntegral.sum _ fun j _ => IsIntegral.sum _ fun i _ => hwI.pow i
      have hid : (N : Ω) = (1 - w) * c := by
        rw [hc, Finset.mul_sum]
        simp_rw [mul_neg_geom_sum]
        rw [Finset.sum_sub_distrib, geom_sum_eq hw1, hwN, sub_self, zero_div, sub_zero]
        simp
      have hNv : A.valuation (N : Ω) = 1 := by
        rw [hNdef, Nat.cast_pow, map_pow, hl1', one_pow]
      have hlt : A.valuation (N : Ω) < 1 := by
        rw [hid, map_mul, Valuation.map_sub_swap]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint c hcI)) hval
      rw [hNv] at hlt
      exact lt_irrefl _ hlt
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    rw [MonoidHom.mem_ker]
    change cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G k Ω) Ω σ) = 1
    apply Units.ext
    rw [Units.val_one]
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_one]
    refine (modularCyclotomicCharacter.unique _ _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ (l ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ht, Units.val_one]
    change σ (t : Ω) = _
    rw [hfix n _ ht']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp at ht'
      simp [ht']
    · haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
      rw [ZMod.val_one, pow_one]
