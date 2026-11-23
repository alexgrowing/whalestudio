import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.TameInertiaTowers.TowerFieldFoundations

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Mu

variable {L : Type} [Field L] [NumberField L]

theorem mu_le_ram (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (k : ℕ) (hk : ((p : ℤ) : 𝓞 L) ∈ Q ^ k) :
    k ≤ Q.ramificationIdx ℤ := by
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) = span {((p : ℤ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, algebraMap_int_eq, eq_intCast]
  have hne0 : ((p : ℤ) : 𝓞 L) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 L) L) h0
    have h2 : (p : L) = 0 := by simpa using h1
    exact hp.out.ne_zero (by exact_mod_cast h2)
  have hne : Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hne0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(p : ℤ)}) Q hne]
  have hdvd : Q ^ k ∣ Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_singleton_le_iff_mem]
    exact hk
  have hQ : ¬ IsUnit Q := by
    rw [Ideal.isUnit_iff]
    exact Ideal.IsPrime.ne_top ‹_›
  first
    | exact (FiniteMultiplicity.of_not_isUnit hQ hne).le_multiplicity_of_pow_dvd hdvd
    | exact (multiplicity_finite_of_not_isUnit hQ hne).le_multiplicity_of_pow_dvd hdvd
    | exact ((pow_dvd_iff_le_multiplicity (FiniteMultiplicity.of_not_isUnit hQ hne)).mp hdvd)

theorem mu_mem_pow (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (η : L) (hη : IsPrimitiveRoot η p) :
    ((p : ℤ) : 𝓞 L) ∈ Q ^ (p - 1) := by
  have hp0 : 0 < p := hp.out.pos
  have hint : IsIntegral ℤ η := hη.isIntegral hp0
  let η' : 𝓞 L := ⟨η, hint⟩
  have hmapη : algebraMap (𝓞 L) L η' = η := rfl
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := by
    first
      | exact FaithfulSMul.algebraMap_injective (𝓞 L) L
      | exact NumberField.RingOfIntegers.coe_injective
  have hη' : IsPrimitiveRoot η' p := by
    refine ⟨hinj ?_, fun l hl => hη.dvd_of_pow_eq_one l ?_⟩
    · rw [map_pow, hmapη, map_one]
      exact hη.pow_eq_one
    · rw [← hmapη, ← map_pow, hl, map_one]
  have hprod : ((p : ℤ) : 𝓞 L) = ∏ μ ∈ primitiveRoots p (𝓞 L), (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hη', Polynomial.eval_prod] at h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
    rw [Int.cast_natCast, ← h1]
  have hmemQ : ((p : ℤ) : 𝓞 L) ∈ Q := by
    have hover : span {(p : ℤ)} = Ideal.under ℤ Q := Ideal.LiesOver.over
    have h1 : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [← hover]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap, algebraMap_int_eq, eq_intCast] at h1
    exact h1
  rw [hprod] at hmemQ
  obtain ⟨μ0, hμ0mem, hμ0Q⟩ : ∃ μ ∈ primitiveRoots p (𝓞 L), 1 - μ ∈ Q := by
    first
      | exact Ideal.IsPrime.prod_mem_iff.mp hmemQ
      | exact (Ideal.IsPrime.prod_mem_iff_exists_mem ‹Q.IsPrime›).mp hmemQ
      | exact (Ideal.IsPrime.prod_mem_iff ‹Q.IsPrime›).1 hmemQ
  have hall : ∀ μ ∈ primitiveRoots p (𝓞 L), 1 - μ ∈ Q := by
    intro μ hμ
    have hμ0p : IsPrimitiveRoot μ0 p := (mem_primitiveRoots hp0).mp hμ0mem
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp0).mp hμ
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    obtain ⟨i, -, hi⟩ := hμ0p.eq_pow_of_pow_eq_one hμp.pow_eq_one
    rw [← hi]
    have hd : 1 - μ0 ∣ 1 - μ0 ^ i := by simpa [one_pow] using sub_dvd_pow_sub_pow 1 μ0 i
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact Ideal.mul_mem_right c Q hμ0Q
  rw [hprod]
  have h2 := Ideal.prod_mem_prod (I := fun _ => Q) hall
  rw [Finset.prod_const, IsPrimitiveRoot.card_primitiveRoots hη', Nat.totient_prime hp.out] at h2
  exact h2

theorem mu_card_le_two {G : Type*} [One G] (f : Gal(L/ℚ) → G) (hinj : Function.Injective f)
    (t : G) (H : Subgroup Gal(L/ℚ)) (hH : ∀ ρ ∈ H, f ρ = 1 ∨ f ρ = t) : Nat.card H ≤ 2 := by
  classical
  let g : H → ({1, t} : Set G) := fun ρ => ⟨f ρ, by rcases hH ρ ρ.2 with h | h <;> simp [h]⟩
  have hg : Function.Injective g := fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))
  calc Nat.card H ≤ Nat.card ({1, t} : Set G) := Nat.card_le_card_of_injective g hg
    _ = ({1, t} : Set G).ncard := by first | exact Nat.card_coe_set_eq _ | exact Set.Nat.card_coe_set_eq _
    _ ≤ 2 := (Set.ncard_insert_le 1 {t}).trans (by simp)

variable {e q d : ℕ} {ζ a b : L}

theorem mu_ram_bound (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    Q.ramificationIdx ℤ ≤ 2 ∧ (p ≠ q → p ≠ d → Q.ramificationIdx ℤ ≤ 1) := by
  obtain ⟨hGal, -, -, hbij⟩ := Formalism.FrobeniusOrbits.Galois.layer_galois hqd h
  haveI := hGal
  rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_card L p Q]
  have hinjF := hbij.1
  have key : p ≠ q → p ≠ d → Nat.card (Q.inertia Gal(L/ℚ)) ≤ 1 := by
    intro hpq hpd
    obtain ⟨⟨σ, hσ⟩, hiff⟩ :=
      Formalism.TwoAdicCyclotomicDecomposition.layerFrob (e + 2) q d (by omega) hqd L ζ a b h p hp2 hpq hpd Q
    have hρ1 : ∀ ρ ∈ Q.inertia Gal(L/ℚ), ρ = 1 := by
      intro ρ hρ
      have hf := Formalism.FrobeniusOrbits.Frob.frob_mul_inertia Q ρ σ hρ hσ
      have A := (hiff _).1 hf
      have B := (hiff _).1 hσ
      have heq : galMap h.1 a b (ρ * σ) = galMap h.1 a b σ :=
        Prod.ext (Units.ext (A.1.trans B.1.symm))
          (Prod.ext (Units.ext (A.2.1.trans B.2.1.symm)) (Units.ext (A.2.2.trans B.2.2.symm)))
      have h3 := hinjF heq
      first
        | exact mul_eq_right.mp h3
        | exact mul_left_eq_self.mp h3
    have hsub : Subsingleton (Q.inertia Gal(L/ℚ)) := by
      constructor
      rintro ⟨ρ, hρ⟩ ⟨ρ', hρ'⟩
      have e1 := hρ1 ρ hρ
      have e2 := hρ1 ρ' hρ'
      subst e1
      subst e2
      rfl
    first
      | exact Nat.card_le_one_iff_subsingleton.mpr hsub
      | exact Finite.card_le_one_iff_subsingleton.mpr hsub
  have tame := Formalism.TwoAdicCyclotomicDecomposition.layerInertiaTame (e + 2) q d (by omega) hqd L ζ a b h
  have two_of : ∀ t : GalL (e + 2), t ^ 2 = 1 →
      (∀ ρ ∈ Q.inertia Gal(L/ℚ), galMap h.1 a b ρ ∈ Subgroup.zpowers t) →
      Nat.card (Q.inertia Gal(L/ℚ)) ≤ 2 := by
    intro t ht hmem
    refine mu_card_le_two (galMap h.1 a b) hinjF t _ ?_
    intro ρ hρ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmem ρ hρ)
    have ht' : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact ht
    rw [← hk, zpow_eq_zpow_emod k ht']
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0 <;> rw [h0] <;> simp
  refine ⟨?_, fun hpq hpd => key hpq hpd⟩
  by_cases hpq : p = q
  · subst hpq
    exact two_of ((1, -1, 1) : GalL (e + 2)) (by simp [sq])
      (fun ρ hρ => (tame.1 Q ρ).1 hρ)
  · by_cases hpd : p = d
    · subst hpd
      exact two_of ((1, 1, -1) : GalL (e + 2)) (by simp [sq])
        (fun ρ hρ => (tame.2 Q ρ).1 hρ)
    · exact (key hpq hpd).trans (by norm_num)

theorem mu_no_odd (hq : HostHyp q d) (hq3 : q ≠ 3) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (η : L) (hη : IsPrimitiveRoot η p) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) (span {(p : ℤ)})
  haveI := hQmax.isPrime
  haveI := hQover
  have h1 := mu_mem_pow p Q η hη
  have h2 := mu_le_ram p Q (p - 1) h1
  have h3 := mu_ram_bound hq.toHypOdd h p hp2 Q
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h31 := h3.1
  have hle : p ≤ 3 := by omega
  have hpq : p ≠ q := by omega
  have hpd : p ≠ d := by
    intro hpd
    have := hq.2.2.2.1
    omega
  have := h3.2 hpq hpd
  omega

theorem mu_no_four (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (y : L)
    (hyE : y ∈ hostE ζ a b) (hy : IsPrimitiveRoot y 4) : False := by
  have hfix : Galois.tau0 hqd h y = y := (Formalism.FrobeniusOrbits.Galois.mem_hostE_iff hqd h y).mp hyE
  have hζ := h.1
  have hτζ : Galois.tau0 hqd h ζ = ζ⁻¹ := by
    have hg := Formalism.FrobeniusOrbits.Galois.galMap_zeta_inversion hqd h
    have hau : hζ.autToPow ℚ (Galois.tau0 hqd h) = -1 := congrArg Prod.fst hg
    have hspec : ζ ^ ((hζ.autToPow ℚ (Galois.tau0 hqd h) : ZMod (2 ^ (e + 2))).val) = Galois.tau0 hqd h ζ := by
      first
        | exact hζ.autToPow_spec ℚ (Galois.tau0 hqd h)
        | exact hζ.autToPow_spec (Galois.tau0 hqd h)
    rw [← hspec, hau]
    set v := (((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2)))).val with hvdef
    have hz : ((v + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
      rw [Nat.cast_add, hvdef, ZMod.natCast_zmod_val]
      simp
    have hv : 2 ^ (e + 2) ∣ v + 1 := by
      first
        | exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hz
        | exact (ZMod.natCast_eq_zero_iff _ _).mp hz
        | exact (ZMod.natCast_self_eq_zero_iff _ _).mp hz
    have h1 := (hζ.pow_eq_one_iff_dvd _).mpr hv
    rw [pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hyN : y ^ (2 ^ (e + 2)) = 1 := by
    rw [show 2 ^ (e + 2) = 4 * 2 ^ e by ring, pow_mul, hy.pow_eq_one, one_pow]
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hyN
  have hτy : Galois.tau0 hqd h y = y⁻¹ := by
    rw [← hj, map_pow, hτζ, inv_pow]
  rw [hτy] at hfix
  have hy0 : y ≠ 0 := hy.ne_zero (by norm_num)
  have hy2 : y ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hfix]
    exact inv_mul_cancel₀ hy0
  have h4 := (hy.pow_eq_one_iff_dvd 2).mp hy2
  norm_num at h4

end Mu

open Mu

theorem hostMu : HostMu := by
  intro e q d hq hq3 L _ _ ζ a b h x hx
  obtain ⟨m, hm, hxm⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hxm⟩
  have hn0 : 0 < orderOf x := orderOf_pos_iff.mpr hfin
  have hxo : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hcoe : ∀ (y : hostE ζ a b) (k : ℕ), IsPrimitiveRoot y k → IsPrimitiveRoot (y : L) k :=
    fun y k hy => IsPrimitiveRoot.coe_submonoidClass_iff.mpr hy
  have h2 : x ^ 2 = 1 := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf x) with ⟨k, hk⟩ | ⟨p, hp, hpn, hodd⟩
    · by_cases hk2 : 2 ≤ k
      · exfalso
        have hsplit : orderOf x = 2 ^ (k - 2) * 4 := by
          rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
        have hy := IsPrimitiveRoot.pow hn0 hxo hsplit
        exact mu_no_four hq.toHypOdd h ((x ^ (2 ^ (k - 2)) : hostE ζ a b) : L)
          (x ^ (2 ^ (k - 2))).2 (hcoe _ _ hy)
      · have hd : orderOf x ∣ 2 := by
          rw [hk]
          exact (pow_dvd_pow 2 (by omega : k ≤ 1)).trans (by norm_num)
        exact orderOf_dvd_iff_pow_eq_one.mp hd
    · exfalso
      obtain ⟨c, hc⟩ := hpn
      have hy := IsPrimitiveRoot.pow hn0 hxo (show orderOf x = c * p by rw [hc, mul_comm])
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) even_two
      exact mu_no_odd hq hq3 h p hp hp2 _ (hcoe _ _ hy)
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)

end Formalism.FrobeniusOrbits
