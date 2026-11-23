import Formalism.SizeWindowBrackets.SmoothedRemainderRealIntegralFormula
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Filter Topology ArithmeticFunction DirichletCharacter

noncomputable section

namespace Formalism.LFunctionChainParameters.LBr2

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

theorem ell_is_log_derivative : EllIsLD1 := by
  intro e q d _ _ ψ
  rfl

theorem g_zeta_eq_g_one : GrowthFunctionEqTrivial := by
  intro y
  unfold Gz Sz G1
  ring

theorem g_psi_eq_g_chi : GPsiIsGchi := by
  intro e q d _ _ ell ψ hψ hell y
  unfold GPsi Gchi
  rw [if_neg hψ, hell]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.1 hn).1
    omega
  have h := primitive_value_primitive (H := HA e) (hostN e q d) q d (recMap e q d) ψ n (NeZero.ne _) hn0
  rw [show primVal (hostData e q d) ψ n = _ from h]
  rfl

theorem g_psi_at_modulus : GPsiHost := by
  intro e q d _ _
  refine ⟨fun ψ hψ y => g_psi_eq_g_chi e q d _ ψ hψ (ell_is_log_derivative e q d ψ) y, fun y => ?_⟩
  unfold GPsi
  rw [if_pos rfl, g_zeta_eq_g_one y]

lemma dirChar_zero (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    dirChar (recMap e q d) (0 : AddChar (E0 × HA e) ℂ) = 1 := by
  apply MulChar.ext
  intro u
  rw [dirChar_unit, MulChar.one_apply_coe]
  rfl

theorem character_of_facts : ChiOfFacts := by
  intro e q d _ _ h ψ
  refine ⟨primitiveCharacter_isPrimitive _, ⟨conductor_dvd_level _, changeLevel_primitiveCharacter _⟩, fun hψ => ?_⟩
  have hne : dirChar (recMap e q d) ψ ≠ 1 := by
    intro h1
    rw [← dirChar_zero e q d] at h1
    exact hψ (dirichlet_character_injective e q d h h1)
  have hc : condOf e q d ψ ≠ 1 := fun h1 => hne (eq_one_iff_conductor_eq_one.2 h1)
  refine ⟨fun h1 => hne ?_, hc⟩
  have h2 := changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ)
  rw [show (dirChar (recMap e q d) ψ).primitiveCharacter = 1 from h1, changeLevel_one] at h2
  exact h2.symm

theorem thin_iff : ThinIff := by
  intro e q d _ _ X' θ
  obtain ⟨h1, h0⟩ := g_psi_at_modulus e q d
  constructor
  · intro h
    refine ⟨fun ψ hψ y hy => ?_, fun y hy => ?_⟩
    · rw [← h1 ψ hψ y]
      exact h ψ y hy
    · have := h 0 y hy
      rwa [h0 y, Complex.norm_real, Real.norm_eq_abs] at this
  · rintro ⟨hA, hB⟩ ψ y hy
    by_cases hψ : ψ = 0
    · subst hψ
      rw [h0 y, Complex.norm_real, Real.norm_eq_abs]
      exact hB y hy
    · rw [h1 ψ hψ y]
      exact hA ψ hψ y hy

lemma sameChar_eq {N : ℕ} [NeZero N] {χ χ' : DirichletCharacter ℂ N} (h : SameChar χ χ') : χ = χ' := by
  apply DFunLike.ext
  intro a
  have := h.2 a.val
  rwa [ZMod.natCast_zmod_val] at this

theorem same_character_g : SameCharG := by
  intro N M _ _ χ χ' h
  obtain ⟨rfl, -⟩ := id h
  obtain rfl := sameChar_eq h
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, Iff.rfl⟩

lemma sameChar_prim {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hM : M ∣ N) (χ' : DirichletCharacter ℂ M)
    (hp : χ'.IsPrimitive) (hχ : χ = changeLevel hM χ') : SameChar χ.primitiveCharacter χ' := by
  have hc : χ.conductor = M := by
    rw [hχ, conductor_changeLevel]
    exact hp
  have key : ∀ (c : ℕ) (χ₀ : DirichletCharacter ℂ c) (hcN : c ∣ N), changeLevel hcN χ₀ = χ → c = M →
      SameChar χ₀ χ' := by
    intro c χ₀ hcN h1 h2
    subst h2
    have h3 : χ₀ = χ' := changeLevel_injective hcN (h1.trans hχ)
    subst h3
    exact ⟨rfl, fun _ => rfl⟩
  exact key _ _ (conductor_dvd_level χ) (changeLevel_primitiveCharacter χ) hc

lemma qc_ne_one (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : qc q ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact h2)
  have h1 := DFunLike.congr_fun h (a : ZMod q)
  rw [qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply_coe] at h1
  norm_num at h1

lemma qc_prim (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : (qc q).IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level (qc q)
  rcases (Nat.dvd_prime Fact.out).1 hd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)
  · exact h

lemma qc_sq (q : ℕ) [Fact q.Prime] : qc q ^ 2 = 1 :=
  ((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)).sq_eq_one

lemma prim_mul {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3

lemma chi_eight_sq : chi8 ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one

lemma chi_eight_primitive : chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level chi8
  have h4 : chi8.conductor ∣ 4 := by
    have hle : chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5

theorem twist_primitive : TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]

section Host
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

lemma qcLift_apply {N l : ℕ} [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) :
    changeLevel h (qc l) (u : ZMod N)
      = ((((quadraticChar (ZMod l)).toUnitHom (ZMod.unitsMap h u) : ℤˣ) : ℤ) : ℂ) := by
  rw [changeLevel_eq_cast_of_dvd]
  unfold qc
  rw [MulChar.ringHomComp_apply]
  simp [ZMod.unitsMap_val]

lemma tw_lift {N t l : ℕ} [Fact l.Prime] (θ : DirichletCharacter ℂ t) (h : t * l ∣ N) :
    changeLevel h (tw θ l) = changeLevel ((Dvd.intro l rfl).trans h) θ
      * changeLevel ((Dvd.intro_left t rfl).trans h) (qc l) := by
  unfold tw
  rw [map_mul, ← changeLevel_trans, ← changeLevel_trans]

lemma psi_split (ψ : AddChar (E0 × HA e) ℂ) (a b : ZMod 2) (t : HA e) :
    ψ ((a, b), t) = ψ ((0, 0), t) * ψ ((0, b), 0) * ψ ((a, 0), 0) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp

lemma psi_pm (ψ : AddChar (E0 × HA e) ℂ) (g : E0 × HA e) (hg : g + g = 0) : ψ g = 1 ∨ ψ g = -1 := by
  have : ψ g * ψ g = 1 := by rw [← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]
  exact mul_self_eq_one_iff.1 this

lemma comp_one (ψ : AddChar (E0 × HA e) ℂ) (f : ZMod 2 → E0 × HA e) (f0 : f 0 = 0) (h1 : ψ (f 1) = 1) (a : ZMod 2) :
    ψ (f a) = 1 := by
  rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
  · rw [f0, AddChar.map_zero_eq_one]
  · exact h1

lemma comp_neg (ψ : AddChar (E0 × HA e) ℂ) (f : ZMod 2 → E0 × HA e) (f0 : f 0 = 0) (h1 : ψ (f 1) = -1) (s : ℤˣ) :
    ψ (f (Multiplicative.toAdd (LHost.sgn2 s))) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [map_one, toAdd_one, f0, AddChar.map_zero_eq_one]
    simp
  · have : Multiplicative.toAdd (LHost.sgn2 (-1)) = 1 := by decide
    rw [this, h1]
    simp

lemma dirChar_prod (ψ : AddChar (E0 × HA e) ℂ) (D2 Dq Dd : DirichletCharacter ℂ (hostN e q d))
    (h2 : ∀ u : (ZMod (hostN e q d))ˣ, D2 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))))
    (hq : ∀ u : (ZMod (hostN e q d))ˣ, Dq (u : ZMod _) = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0))
    (hd : ∀ u : (ZMod (hostN e q d))ˣ, Dd (u : ZMod _) = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0)) :
    dirChar (recMap e q d) ψ = D2 * Dq * Dd := by
  apply MulChar.ext
  intro u
  rw [dirChar_unit, recMap_apply, psi_split, MulChar.mul_apply, MulChar.mul_apply, h2, hq, hd]

lemma compQ_one (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((0, 1), 0) = 1) (u : (ZMod (hostN e q d))ˣ) :
    (1 : DirichletCharacter ℂ (hostN e q d)) (u : ZMod _)
      = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0) := by
  rw [MulChar.one_apply_coe, comp_one ψ (fun a => ((0, a), 0)) rfl h1]

lemma compD_one (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((1, 0), 0) = 1) (u : (ZMod (hostN e q d))ˣ) :
    (1 : DirichletCharacter ℂ (hostN e q d)) (u : ZMod _)
      = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0) := by
  rw [MulChar.one_apply_coe, comp_one ψ (fun a => ((a, 0), 0)) rfl h1]

lemma compQ_neg (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((0, 1), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (q_dvd_hostN e q d) (qc q) (u : ZMod _)
      = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0) := by
  rw [qcLift_apply]
  exact (comp_neg ψ (fun a => ((0, a), 0)) rfl h1 _).symm

lemma compD_neg (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((1, 0), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (d_dvd_hostN e q d) (qc d) (u : ZMod _)
      = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0) := by
  rw [qcLift_apply]
  exact (comp_neg ψ (fun a => ((a, 0), 0)) rfl h1 _).symm

lemma component_two_one (ψ : AddChar (E0 × HA e) ℂ) (h1 : ∀ t : HA e, ψ ((0, 0), t) = 1) (u : (ZMod (hostN e q d))ˣ) :
    (1 : DirichletCharacter ℂ (hostN e q d)) (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
  rw [MulChar.one_apply_coe, h1]

end Host

lemma psC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (psC : AddChar (E0 × H) ℂ) g = if g.1.2 = 0 then 1 else -1 := rfl

lemma chC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := rfl

lemma chpsC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chpsC : AddChar (E0 × H) ℂ) g = (if g.1.1 = 0 then 1 else -1) * (if g.1.2 = 0 then 1 else -1) := rfl

lemma one_ne_zero2 : (1 : ZMod 2) ≠ 0 := by decide

lemma change_level_one {N : ℕ} (h : 1 ∣ N) : changeLevel h one1 = 1 := changeLevel_one h

theorem quadratic_characters_input : HostQuadChars := by
  intro e q d _ _ h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have p1 : one1.IsPrimitive := isPrimitive_one_level_one
  have pq := (twist_primitive.2 1 one1 q p1 hq2 (Nat.coprime_one_right q)).1
  have pd := (twist_primitive.2 1 one1 d p1 hd2 (Nat.coprime_one_right d)).1
  have pqd := (twist_primitive.2 (1 * q) (tw one1 q) d pq hd2
    (by rw [one_mul]; exact (Nat.coprime_primes h.2.1 h.1).2 hqd.symm)).1
  have dq : 1 * q ∣ hostN e q d := by rw [one_mul]; exact q_dvd_hostN e q d
  have dd : 1 * d ∣ hostN e q d := by rw [one_mul]; exact d_dvd_hostN e q d
  have dqd : 1 * q * d ∣ hostN e q d := ⟨2 ^ (e + 2), by unfold hostN; ring⟩
  refine ⟨sameChar_prim _ dq _ pq ?_, sameChar_prim _ dd _ pd ?_, sameChar_prim _ dqd _ pqd ?_⟩
  · rw [tw_lift, change_level_one, dirChar_prod psC 1 (changeLevel (q_dvd_hostN e q d) (qc q)) 1
      (component_two_one _ (fun t => by simp [psC_apply])) (compQ_neg _ (by simp [psC_apply]))
      (compD_one _ (by simp [psC_apply])), mul_one]
  · rw [tw_lift, change_level_one, dirChar_prod chC 1 1 (changeLevel (d_dvd_hostN e q d) (qc d))
      (component_two_one _ (fun t => by simp [chC_apply])) (compQ_one _ (by simp [chC_apply]))
      (compD_neg _ (by simp [chC_apply])), mul_one]
  · rw [tw_lift, tw_lift, change_level_one, dirChar_prod chpsC 1 (changeLevel (q_dvd_hostN e q d) (qc q))
      (changeLevel (d_dvd_hostN e q d) (qc d))
      (component_two_one _ (fun t => by simp [chpsC_apply])) (compQ_neg _ (by simp [chpsC_apply]))
      (compD_neg _ (by simp [chpsC_apply]))]

lemma quad_ne_zero (e : ℕ) : (psC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧ (chC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧
    (chpsC : AddChar (E0 × HA e) ℂ) ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := DFunLike.congr_fun h (((0, 1), 0) : E0 × HA e)
    rw [psC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
  · have := DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)
    rw [chC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
  · have := DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)
    rw [chpsC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this

theorem valuesIff_valid : ValuesIff := by
  intro e q d _ _ h x ε C
  obtain ⟨s1, s2, s3⟩ := quadratic_characters_input e q d h
  obtain ⟨n1, n2, n3⟩ := quad_ne_zero e
  obtain ⟨l1, g1, -⟩ := same_character_g _ _ _ _ s1
  obtain ⟨l2, g2, -⟩ := same_character_g _ _ _ _ s2
  obtain ⟨l3, g3, -⟩ := same_character_g _ _ _ _ s3
  have hG := (g_psi_at_modulus e q d).1
  have hL := ell_is_log_derivative e q d
  constructor
  · intro hv
    have v1 := hv psC (Or.inl rfl)
    have v2 := hv chC (Or.inr (Or.inl rfl))
    have v3 := hv chpsC (Or.inr (Or.inr rfl))
    rw [hG _ n1, hL, g1, l1] at v1
    rw [hG _ n2, hL, g2, l2] at v2
    rw [hG _ n3, hL, g3, l3] at v3
    exact ⟨v1, v2, v3⟩
  · rintro ⟨v1, v2, v3⟩ ψ (rfl | rfl | rfl)
    · rw [hG _ n1, hL, g1, l1]; exact v1
    · rw [hG _ n2, hL, g2, l2]; exact v2
    · rw [hG _ n3, hL, g3, l3]; exact v3

theorem prime_congruence_conditions : PrimeCongruenceHypotheses := by
  intro q d hq hd h8 h16 hs
  obtain ⟨r, s, hrs, hr, hs⟩ := hs
  refine ⟨hq, hd, h8, h16, ?_⟩
  have := Fact.mk hq
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ZMod q) * (((d + 1) / 4 : ℕ) : ZMod q) = (d : ZMod q) + 1 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod q) h4
  have two : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hq.two_le
    omega
  have sqr : ∀ t : ZMod q, t ^ 2 - t + (((d + 1) / 4 : ℕ) : ZMod q) = 0 → (2 * t - 1) ^ 2 = -(d : ZMod q) := by
    intro t ht
    linear_combination 4 * ht - h4'
  have hne : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    have h0' : -(d : ZMod q) = 0 := by exact_mod_cast h0
    have e1 : 2 * r - 1 = 0 := by
      have := sqr r hr
      rw [h0'] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have e2 : 2 * s - 1 = 0 := by
      have := sqr s hs
      rw [h0'] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    apply hrs
    have : (2 : ZMod q) * (r - s) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h two
    · exact sub_eq_zero.1 h
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff q hne]
  refine ⟨2 * r - 1, ?_⟩
  have := sqr r hr
  push_cast
  rw [← this]
  ring

section Real
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

lemma H_gen (e : ℕ) (t : FrobeniusOrbits.HGrp e) : ∃ k : ℕ, t = (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k := by
  obtain ⟨-, -, -, -, -, -, -, -, ι, hι⟩ := FrobeniusOrbits.hostGroup e
  refine ⟨(Multiplicative.toAdd (ι.symm t)).val, ?_⟩
  rw [← hι, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd,
    MulEquiv.apply_symm_apply]

lemma psi_H_pow (ψ : AddChar (E0 × HA e) ℂ) (g : FrobeniusOrbits.HGrp e) (k : ℕ) :
    ψ ((0, 0), Additive.ofMul (g ^ k)) = ψ ((0, 0), Additive.ofMul g) ^ k := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [Prod.smul_mk, ofMul_pow]

lemma chi_eight_lift_values (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) :
    changeLevel h8 chi8 ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 ∧
    changeLevel h8 chi8 ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = -1 := by
  constructor
  · have h := changeLevel_eq_cast_of_dvd' chi8 h8 (a := -1) (by
      exact (isCoprime_one_left).neg_left)
    have e1 : (((-1 : ℤ)) : ZMod (2 ^ (e + 2))) = ((-1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) := by
      simp
    rw [e1] at h
    rw [h, chi8, MulChar.ringHomComp_apply]
    have : ZMod.χ₈ ((-1 : ℤ) : ZMod 8) = 1 := by decide
    rw [this]
    simp
  · have h := changeLevel_eq_cast_of_dvd' chi8 h8 (a := 5) (by
      push_cast
      apply IsCoprime.pow_right
      rw [Int.isCoprime_iff_gcd_eq_one]
      decide)
    have e1 : (((5 : ℤ)) : ZMod (2 ^ (e + 2))) = ((TwoAdicCyclotomicDecomposition.u5 (e + 2) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) := by
      unfold TwoAdicCyclotomicDecomposition.u5
      rw [ZMod.coe_unitOfCoprime]
      simp
    rw [e1] at h
    rw [h, chi8, MulChar.ringHomComp_apply]
    have : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
    rw [this]
    simp

lemma chi_eight_lift_class (e : ℕ) (h8 : 8 ∣ 2 ^ (e + 2)) (v : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ)
    (hk : FrobeniusOrbits.hcl e v = (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k) :
    changeLevel h8 chi8 (v : ZMod (2 ^ (e + 2))) = (-1) ^ k := by
  obtain ⟨hm, h5⟩ := chi_eight_lift_values e h8
  set F := (changeLevel h8 chi8).toUnitHom with hF
  have hFm : F (-1) = 1 := by
    apply Units.ext
    rw [hF, MulChar.coe_toUnitHom, hm]
    rfl
  have hF5 : ((F (TwoAdicCyclotomicDecomposition.u5 (e + 2)) : ℂˣ) : ℂ) = -1 := by
    rw [hF, MulChar.coe_toUnitHom, h5]
  have hmem : v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ) := by
    apply QuotientGroup.eq.1
    exact hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h1 : F (v⁻¹ * (TwoAdicCyclotomicDecomposition.u5 (e + 2)) ^ k) = 1 := by
    rw [← hj, map_zpow, hFm, one_zpow]
  rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h1
  rw [← MulChar.coe_toUnitHom, ← hF, h1, Units.val_pow_eq_pow_val, hF5]

lemma component_two_neg (ψ : AddChar (E0 × HA e) ℂ) (h8 : 8 ∣ 2 ^ (e + 2))
    (h1 : ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (h8.trans (two_dvd_hostN e q d)) chi8 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
  obtain ⟨k, hk⟩ := H_gen e (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))
  rw [hk, psi_H_pow, h1, changeLevel_trans chi8 h8 (two_dvd_hostN e q d), changeLevel_eq_cast_of_dvd,
    ← chi_eight_lift_class e h8 _ k hk, ZMod.unitsMap_val]

end Real
section Real2
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

lemma real_cases (h : FrobeniusOrbits.HostHyp q d) (ψ : AddChar (E0 × HA e) ℂ) {t : ℕ} (θ : DirichletCharacter ℂ t)
    (ht : t ∣ 2 ^ (e + 2)) (hθ : θ.IsPrimitive)
    (h2 : ∀ u : (ZMod (hostN e q d))ˣ, changeLevel (ht.trans (two_dvd_hostN e q d)) θ (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u)))) :
    dirChar (recMap e q d) ψ = changeLevel (ht.trans (two_dvd_hostN e q d)) θ ∨
    SameChar (chiOf e q d ψ) (tw θ q) ∨ SameChar (chiOf e q d ψ) (tw θ d) ∨
    SameChar (chiOf e q d ψ) (tw (tw θ q) d) := by
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have cq : q.Coprime t := Nat.Coprime.coprime_dvd_right ht
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2))
  have cd : d.Coprime t := Nat.Coprime.coprime_dvd_right ht
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes h.2.1 Nat.prime_two).2 hd2))
  have pq := (twist_primitive.2 t θ q hθ hq2 cq).1
  have pd := (twist_primitive.2 t θ d hθ hd2 cd).1
  have pqd := (twist_primitive.2 (t * q) (tw θ q) d pq hd2
    (Nat.Coprime.mul_right cd ((Nat.coprime_primes h.2.1 h.1).2 hqd.symm))).1
  obtain ⟨c, hc⟩ := ht
  have dq : t * q ∣ hostN e q d := ⟨c * d, by unfold hostN; rw [hc]; ring⟩
  have dd : t * d ∣ hostN e q d := ⟨c * q, by unfold hostN; rw [hc]; ring⟩
  have dqd : t * q * d ∣ hostN e q d := ⟨c, by unfold hostN; rw [hc]; ring⟩
  have z1 : (((0, 1), 0) : E0 × HA e) + ((0, 1), 0) = 0 :=
    Prod.ext (Prod.ext (by simp) (show (1 : ZMod 2) + 1 = 0 by decide)) (by simp)
  have z2 : (((1, 0), 0) : E0 × HA e) + ((1, 0), 0) = 0 :=
    Prod.ext (Prod.ext (show (1 : ZMod 2) + 1 = 0 by decide) (by simp)) (by simp)
  rcases psi_pm ψ _ z1 with eq1 | eq1 <;> rcases psi_pm ψ _ z2 with ed1 | ed1
  · left
    rw [dirChar_prod ψ _ 1 1 h2 (compQ_one ψ eq1) (compD_one ψ ed1), mul_one, mul_one]
  · right; right; left
    refine sameChar_prim _ dd _ pd ?_
    rw [tw_lift, dirChar_prod ψ _ 1 _ h2 (compQ_one ψ eq1) (compD_neg ψ ed1), mul_one]
  · right; left
    refine sameChar_prim _ dq _ pq ?_
    rw [tw_lift, dirChar_prod ψ _ _ 1 h2 (compQ_neg ψ eq1) (compD_one ψ ed1), mul_one]
  · right; right; right
    refine sameChar_prim _ dqd _ pqd ?_
    rw [tw_lift, tw_lift, dirChar_prod ψ _ _ _ h2 (compQ_neg ψ eq1) (compD_neg ψ ed1)]

end Real2

theorem real_characters_input : HostRealChars := by
  intro e q d _ _ h ψ hsq
  have hD : dirChar (recMap e q d) ψ ^ 2 = 1 := by
    rw [← changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ), ← map_pow,
      show (dirChar (recMap e q d) ψ).primitiveCharacter ^ 2 = 1 from hsq, map_one]
  have hreal : ∀ g : E0 × HA e, ψ g = 1 ∨ ψ g = -1 := by
    intro g
    obtain ⟨u, hu⟩ := recSurjective_valid e q d h (Multiplicative.ofAdd g)
    have h1 := DFunLike.congr_fun hD (u : ZMod (hostN e q d))
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, dirChar_unit, hu, toAdd_ofAdd] at h1
    exact mul_self_eq_one_iff.1 (by rw [← sq]; exact h1)
  rcases hreal ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) with h5 | h5
  · have hall : ∀ t : HA e, ψ ((0, 0), t) = 1 := by
      intro t
      obtain ⟨k, hk⟩ := H_gen e (Additive.toMul t)
      have : t = Additive.ofMul ((FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k) := by rw [← hk]; rfl
      rw [this, psi_H_pow, h5, one_pow]
    have h2 : ∀ u : (ZMod (hostN e q d))ˣ,
        changeLevel ((one_dvd (2 ^ (e + 2))).trans (two_dvd_hostN e q d)) one1 (u : ZMod _)
          = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
      intro u
      rw [change_level_one]
      exact component_two_one ψ hall u
    rcases real_cases h ψ one1 (one_dvd _) isPrimitive_one_level_one h2 with c | c | c | c
    · left
      rw [change_level_one, ← dirChar_zero e q d] at c
      exact dirichlet_character_injective e q d h c
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
  · have he : e ≠ 0 := by
      rintro rfl
      obtain ⟨-, -, -, -, -, -, -, ho, -⟩ := FrobeniusOrbits.hostGroup 0
      rw [pow_zero, orderOf_eq_one_iff] at ho
      rw [ho] at h5
      have h0 : ψ ((0, 0), Additive.ofMul (1 : FrobeniusOrbits.HGrp 0)) = 1 := AddChar.map_zero_eq_one ψ
      rw [h0] at h5
      norm_num at h5
    have h8 : 8 ∣ 2 ^ (e + 2) := by
      obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
      exact ⟨2 ^ e', by rw [Nat.succ_eq_add_one]; ring⟩
    rcases real_cases h ψ chi8 h8 chi_eight_primitive (component_two_neg ψ h8 h5) with c | c | c | c
    · exact Or.inr (Or.inl (sameChar_prim _ _ _ chi_eight_primitive c))
    · exact Or.inr (Or.inr (Or.inr (Or.inl c)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c))))))

theorem modulus_formula : HostNIs := by
  intro e q d
  unfold hostN
  ring

lemma zeroFreeBox_same {N M : ℕ} [NeZero N] [NeZero M] {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ M}
    (hs : SameChar χ χ') {Q : ℝ} (h : ZeroFreeBox Q χ') : ZeroFreeBox Q χ := by
  intro s h1 h2
  rw [(same_character_g _ _ _ _ hs).2.2.2.1]
  exact h s h1 h2

theorem thin_one_of : ThinOneOf := by
  rintro ⟨c, K, hc, hK⟩ ε c' hε
  have T1 : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have T2 : Tendsto (fun x : ℝ => c / 2 * x ^ (ε / 24) - c') atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_rpow_atTop (by positivity : 0 < ε / 24)).const_mul_atTop (by positivity))
  have T3 : Tendsto (fun x : ℝ => Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c'))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (T1.atTop_mul_atTop₀ T2)
  have E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in atTop, 5 ≤ x ^ (ε / 3) := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 5
  have E3 := T3.eventually_ge_atTop (max K 0)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (E1.and (E2.and E3))
  refine ⟨x₀, fun x hx y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set X := x ^ (ε / 3) with hX
  have hexp : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogy : X / 4 ≤ Real.log y := by
    have h4 : Real.log (Real.exp X / 3) ≤ Real.log y := Real.log_le_log (by positivity) hy
    rw [Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp] at h4
    linarith
  have hs : x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y) := by
    apply Real.le_sqrt_of_sq_le
    have : (x ^ (ε / 6)) ^ 2 = X := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    linarith
  have hsplit : x ^ (ε / 6) = x ^ (ε / 8) * x ^ (ε / 24) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [← g_zeta_eq_g_one y]
  calc |Gz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y)) := hK y hy2
    _ ≤ max K 0 * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max K 0 * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by
        have h0 : 0 ≤ max K 0 := le_max_right _ _
        have h5 : Real.exp (-c * Real.sqrt (Real.log y)) ≤ Real.exp (-c * (x ^ (ε / 6) / 2)) :=
          Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c')) * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by
        gcongr
    _ = y * Real.exp (-c' * x ^ (ε / 8)) := by
        rw [mul_right_comm, ← Real.exp_add, mul_comm]
        congr 2
        rw [hsplit]
        ring

lemma pow_mul_exp_neg_le (n : ℕ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(b * t)) ≤ (n.factorial : ℝ) / b ^ n := by
  have h := Real.pow_div_factorial_le_exp (b * t) (by positivity) n
  have h2 : (b * t) ^ n ≤ (n.factorial : ℝ) * Real.exp (b * t) := by
    rwa [div_le_iff₀' (by positivity)] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  calc t ^ n * b ^ n = (b * t) ^ n := by rw [mul_pow]; ring
    _ ≤ _ := h2

lemma thin_caseA (a A μ s R : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hμs : μ ≤ s) (hsR : R / 2 ≤ s) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) := by
  have hs2 : 2 ≤ s := by linarith
  have hM0 : 0 < μ + s := by linarith
  have hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 4 * s) + -(a / 8 * R) := by
    have h8 : s / 2 ≤ s ^ 2 / (μ + s) := by
      rw [div_le_div_iff₀ (by norm_num) hM0]
      nlinarith
    have e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s))) := by ring
    have m1 := mul_le_mul_of_nonneg_left h8 ha.le
    have m2 := mul_le_mul_of_nonneg_left hsR ha.le
    rw [e]
    linarith
  have hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * s ^ 6 := by
    have h9 : μ + s + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    calc (μ + s + s ^ 2) ^ 3 ≤ (2 * s ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h9 3
      _ = 8 * s ^ 6 := by ring
  have hK := pow_mul_exp_neg_le 6 (a / 4) s (by positivity) (by linarith)
  have hE := Real.exp_le_exp.2 hexpo
  calc A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ A * (8 * s ^ 6) * Real.exp (-(a / 4 * s) + -(a / 8 * R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcube hA) hE (Real.exp_pos _).le (by positivity)
    _ = 8 * A * (s ^ 6 * Real.exp (-(a / 4 * s))) * Real.exp (-(a / 8 * R)) := by
        rw [Real.exp_add]; ring
    _ ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le

lemma thin_caseB (a A μ s R Lb : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hs0 : 0 ≤ s) (hsμ : s < μ)
    (hμL : μ ≤ Lb) (hv : Lb * R / 2 ≤ s ^ 2) (hL6 : Lb ^ 6 = R ^ 10) (hR0 : 0 ≤ R) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) := by
  have hM0 : 0 < μ + s := by linarith
  have hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 8 * R) + -(a / 8 * R) := by
    have h8 : R / 4 ≤ s ^ 2 / (μ + s) := by
      rw [div_le_div_iff₀ (by norm_num) hM0]
      have h10 : μ + s ≤ 2 * Lb := by linarith
      have h12 : R * (μ + s) ≤ R * (2 * Lb) := mul_le_mul_of_nonneg_left h10 hR0
      linarith
    have e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s))) := by ring
    have m1 := mul_le_mul_of_nonneg_left h8 ha.le
    rw [e]
    linarith
  have hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * R ^ 10 := by
    have h9 : μ + s + s ^ 2 ≤ 2 * Lb ^ 2 := by
      have k1 : s ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hs0 hsμ.le 2
      have k2 : μ ^ 2 ≤ Lb ^ 2 := pow_le_pow_left₀ (by linarith) hμL 2
      have k3 : 2 * μ ≤ μ ^ 2 := by nlinarith
      linarith
    calc (μ + s + s ^ 2) ^ 3 ≤ (2 * Lb ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h9 3
      _ = 8 * Lb ^ 6 := by ring
      _ = 8 * R ^ 10 := by rw [hL6]
  have hK := pow_mul_exp_neg_le 10 (a / 8) R (by positivity) hR0
  have hE := Real.exp_le_exp.2 hexpo
  calc A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ A * (8 * R ^ 10) * Real.exp (-(a / 8 * R) + -(a / 8 * R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcube hA) hE (Real.exp_pos _).le (by positivity)
    _ = 8 * A * (R ^ 10 * Real.exp (-(a / 8 * R))) * Real.exp (-(a / 8 * R)) := by
        rw [Real.exp_add]; ring
    _ ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le

lemma thin_num (ε a A : ℝ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ μ v : ℝ, 2 ≤ μ → μ ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 + 2 → x ^ (ε / 3) / 2 ≤ v →
      A * (μ + Real.sqrt v + v) ^ 3 * Real.exp (-a * v / (μ + Real.sqrt v)) ≤ Real.exp (-(a / 16) * x ^ (ε / 8)) := by
  set K6 : ℝ := ((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6 with hK6
  set K10 : ℝ := ((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10 with hK10
  have TR : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in atTop, 8 ≤ x ^ (ε / 3) := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 8
  have E3 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 2 * ‖x ^ (ε / 480)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < ε / 480)).bound (by norm_num)
  have E4 : ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ (5 * ε / 24) :=
    (tendsto_rpow_atTop (by positivity : 0 < 5 * ε / 24)).eventually_ge_atTop 4
  have E5 : ∀ᶠ x : ℝ in atTop, max (8 * A * K6) (8 * A * K10) ≤ Real.exp (a / 16 * x ^ (ε / 8)) :=
    (Real.tendsto_exp_atTop.comp (TR.const_mul_atTop (by positivity : 0 < a / 16))).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (E1.and (E2.and (E3.and (E4.and E5))))
  refine ⟨x₀, fun x hx μ v hμ2 hμ hv => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = x ^ (ε / 8) := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = x ^ (5 * ε / 24) := ⟨_, rfl⟩
  rw [← hR] at h5 ⊢
  rw [← hLb] at h4
  have hR1 : 1 ≤ R := hR ▸ Real.one_le_rpow h1 (by positivity)
  have hRL : R ≤ Lb := by
    rw [hR, hLb]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hP3 : x ^ (ε / 3) = Lb * R := by
    rw [hLb, hR, ← Real.rpow_add hx0]
    congr 1
    ring
  have hL6 : Lb ^ 6 = R ^ 10 := by
    rw [hLb, hR, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hμL : μ ≤ Lb := by
    have hp : 0 ≤ x ^ (ε / 480) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp] at h3
    have hlog2 : Real.log x ^ 2 ≤ 1 / 4 * x ^ (ε / 240) := by
      have e : x ^ (ε / 240) = x ^ (ε / 480) * x ^ (ε / 480) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      rw [e, ← sq_abs]
      nlinarith [abs_nonneg (Real.log x)]
    have h6 : x ^ (ε / 5) * x ^ (ε / 240) ≤ Lb := by
      rw [← Real.rpow_add hx0, hLb]
      apply Real.rpow_le_rpow_of_exponent_le h1
      linarith
    have hp5 : 0 ≤ x ^ (ε / 5) := by positivity
    have h7 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 1 / 2 * Lb := by
      calc 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (1 / 4 * x ^ (ε / 240)) := by gcongr
        _ = 1 / 2 * (x ^ (ε / 5) * x ^ (ε / 240)) := by ring
        _ ≤ 1 / 2 * Lb := by gcongr
    linarith
  have hv4 : 4 ≤ v := by linarith
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt v := ⟨_, rfl⟩
  have hsv : v = s ^ 2 := by rw [hs]; exact (Real.sq_sqrt hv0).symm
  have hs2 : 2 ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    linarith
  rw [← hs, hsv]
  have hvL : Lb * R / 2 ≤ s ^ 2 := by rw [← hsv, ← hP3]; exact hv
  have hfin : ∀ Kc : ℝ, 8 * A * Kc ≤ Real.exp (a / 16 * R) →
      8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (-(a / 16) * R) := by
    intro Kc hKc
    calc 8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (a / 16 * R) * Real.exp (-(a / 8 * R)) :=
          mul_le_mul_of_nonneg_right hKc (Real.exp_pos _).le
      _ = Real.exp (-(a / 16) * R) := by rw [← Real.exp_add]; congr 1; ring
  by_cases hcase : μ ≤ s
  · have hsR : R / 2 ≤ s := by
      have h13 : (R / 2) ^ 2 ≤ s ^ 2 := by
        have h14 : R * R ≤ Lb * R := mul_le_mul_of_nonneg_right hRL (by linarith)
        nlinarith
      exact (abs_le_of_sq_le_sq' h13 (by linarith)).2
    exact (thin_caseA a A μ s R ha hA hμ2 hcase hsR).trans (hfin K6 (le_trans (le_max_left _ _) h5))
  · rw [not_le] at hcase
    exact (thin_caseB a A μ s R Lb ha hA hμ2 (by linarith) hcase hμL hvL hL6 (by linarith)).trans
      (hfin K10 (le_trans (le_max_right _ _) h5))

lemma gchi_eq_schi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) :
    Gchi χ y = Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y := by
  unfold Gchi Formalism.ZeroFreeDirichlet.Schi Formalism.ZeroFreeDirichlet.negLD logDerivLAtOne
  ring

set_option maxHeartbeats 1000000 in
theorem smooth_weight_general : SmoothGen := by
  intro hP hRS hD hRight c₁ hc₁ hc₁'
  obtain ⟨CD, hCD⟩ := hD c₁ hc₁ hc₁'
  obtain ⟨C₀, hC₀, hR⟩ := hRight
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
      16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
    have ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
    have ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))
    have ha4 : 0 ≤ 8 / c₁ := by positivity
    rw [hAdef]; linarith
  refine ⟨2 * A, by positivity, ?_⟩
  intro q _ χ hχ hE y hy
  have hD' : ∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion (c₁ / 2) q s → (∀ β ∈ (∅ : Finset ℝ), s ≠ (β : ℂ)) →
      ‖Formalism.ZeroFreeDirichlet.negLD χ s + ∑ β ∈ (∅ : Finset ℝ), 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 :=
    fun s h1 h2 => (hCD q χ ∅ hχ hE s h1 h2).trans
      (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy0 : 0 < y := by linarith
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = Real.log y := ⟨_, rfl⟩
  have hv0 : 0 < v := hv ▸ Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt v := ⟨_, rfl⟩
  have hvs : v = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hv0.le).symm
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hv0
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.log q + 2 + s := ⟨_, rfl⟩
  have hM2 : 2 ≤ M := by rw [hM]; linarith
  have hMs : s ≤ M := by rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = c₁ / 16 * v / M := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hτM : τ * M = c₁ / 16 * v := by rw [hτ]; field_simp
  have hτs : τ ≤ s := by
    have h1 : τ * M ≤ s * M := by
      rw [hτM, hvs]
      have : c₁ / 16 * s ^ 2 ≤ 1 * s ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
      have : s * s ≤ s * M := mul_le_mul_of_nonneg_left hMs hs0.le
      nlinarith
    exact le_of_mul_le_mul_right h1 hM0
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp τ := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-τ) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp hτ0
  have hT0 : 0 < T := by linarith
  have hTX : T * X = 1 := by rw [hTdef, hXdef, ← Real.exp_add]; simp
  have hX0 : 0 < X := by rw [hXdef]; exact Real.exp_pos _
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2)) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hmain⟩ :=
    Formalism.ZeroFreeDirichlet.chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ ∅ hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm
  rw [Finset.sum_empty, add_zero, ← gchi_eq_schi, ← hv] at hmain
  have hlogT : Real.log (T + 2) ≤ 2 + τ := by
    rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have := mul_le_mul_of_nonneg_right h3 hT0.le
    linarith
  have hLM : L ≤ M := by
    rw [hLdef, Real.log_mul (by linarith) (by linarith), hM]
    linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hW1 : 1 ≤ M + v := by linarith
  have hP1 : 1 ≤ (M + v) ^ 3 := one_le_pow₀ hW1
  have hW3 : M + v ≤ (M + v) ^ 3 := le_self_pow₀ hW1 (by norm_num)
  have h23 : (M + v) ^ 2 ≤ (M + v) ^ 3 := pow_le_pow_right₀ hW1 (by norm_num)
  have hLW : L ≤ M + v := by linarith
  have hℓP : v ≤ (M + v) ^ 3 := by linarith
  have hL2P : L ^ 2 ≤ (M + v) ^ 3 := (pow_le_pow_left₀ hL0 hLW 2).trans h23
  have hL3P : L ^ 3 ≤ (M + v) ^ 3 := pow_le_pow_left₀ hL0 hLW 3
  have hLP : L ≤ (M + v) ^ 3 := by linarith
  have hyσ0 : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
  have hterms := Formalism.ZeroFreeDirichlet.perron_error_terms_sum_bound C C₀ c₁ y T X L ((M + v) ^ 3) (y ^ σ₁) v hc₁ hC hC₀ hy0
    hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP
  rw [← hAdef] at hterms
  have htot := hmain.trans hterms
  have hWX : T * y ^ σ₁ ≤ y * X := by
    have hgap : 4 * τ ≤ v * (1 - σ₁) := by
      have h1 : c₁ / (4 * M) ≤ c₁ / (4 * L) := div_le_div_of_nonneg_left hc₁.le (by linarith) (by linarith)
      have h2 : c₁ / (4 * M) ≤ 1 - σ₁ := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hv0.le
      have e : v * (c₁ / (4 * M)) = 4 * τ := by rw [hτ]; field_simp; ring
      linarith
    have hyexp : y = Real.exp v := by rw [hv, Real.exp_log hy0]
    rw [Real.rpow_def_of_pos hy0, ← hv, hTdef, hXdef, hyexp, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have hfinal : ‖Gchi χ y‖ ≤ 2 * A * y * (M + v) ^ 3 * X := by
    calc ‖Gchi χ y‖ ≤ A * (M + v) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * (M + v) ^ 3 * (y * X + y * X) := by gcongr
      _ = 2 * A * y * (M + v) ^ 3 * X := by ring
  have eX : X = Real.exp (-(c₁ / 16) * v / M) := by
    rw [hXdef, hτ]; congr 1; ring
  rw [← hv, ← hsdef, ← hM, ← eX]
  exact hfinal

theorem thin_of_no_exceptional_zero : ThinOfNoExc := by
  intro hP hRS hD hR ε c₁ hε hc₁ hc₁'
  obtain ⟨A, hA, hS⟩ := smooth_weight_general hP hRS hD hR c₁ hc₁ hc₁'
  obtain ⟨x1, hN⟩ := thin_num ε (c₁ / 16) A hε (by positivity) hA
  obtain ⟨x2, hx2⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop (5 : ℝ))
  refine ⟨max x1 x2, fun x hx q _ χ hχ hE hq y hy => ?_⟩
  have h5 : 5 ≤ x ^ (ε / 3) := hx2 x (le_trans (le_max_right _ _) hx)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = x ^ (ε / 3) := ⟨_, rfl⟩
  rw [← hX] at h5 hy
  have hexp : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogy : X / 2 ≤ Real.log y := by
    have h4 : Real.log (Real.exp X / 3) ≤ Real.log y := Real.log_le_log (by positivity) hy
    rw [Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp] at h4
    linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hnum := hN x (le_trans (le_max_left _ _) hx) (Real.log q + 2) (Real.log y) (by linarith) (by linarith)
    (by rw [← hX]; exact hlogy)
  calc ‖Gchi χ y‖ ≤ A * y * (Real.log q + 2 + Real.sqrt (Real.log y) + Real.log y) ^ 3 *
        Real.exp (-(c₁ / 16) * Real.log y / (Real.log q + 2 + Real.sqrt (Real.log y))) := hS q χ hχ hE y hy2
    _ = y * (A * (Real.log q + 2 + Real.sqrt (Real.log y) + Real.log y) ^ 3 *
        Real.exp (-(c₁ / 16) * Real.log y / (Real.log q + 2 + Real.sqrt (Real.log y)))) := by ring
    _ ≤ y * Real.exp (-(c₁ / 16 / 16) * x ^ (ε / 8)) := mul_le_mul_of_nonneg_left hnum hy0.le
    _ = y * Real.exp (-(c₁ / 256) * x ^ (ε / 8)) := by
        congr 2
        ring

theorem no_exceptional_zero_of_real : NoExcOfReal := by
  rintro ⟨c, hc, hZ⟩
  refine ⟨min c (1 / 1000), lt_min hc (by norm_num), (min_le_right _ _).trans (by norm_num), ?_⟩
  intro q _ χ hreal
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  exfalso
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h2le : (2 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by
    have := abs_nonneg s.im
    nlinarith
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := Real.log_le_log (by norm_num) h2le
  have hl2 := Real.log_two_gt_d9
  have hLpos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) := by linarith
  unfold Formalism.ZeroFreeDirichlet.InRegion at hs
  have hs' : Formalism.ZeroFreeDirichlet.InRegion c q s := by
    unfold Formalism.ZeroFreeDirichlet.InRegion
    have : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q : ℝ) * (|s.im| + 2)) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith
  obtain ⟨h2, -, him, -, -⟩ := hZ q χ s hs' hz
  have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hσ : 1 - 1 / 400 < s.re := by
    have h3 : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 1000) / (1 / 2) :=
      div_le_div₀ (by norm_num) (min_le_right _ _) (by norm_num) (by linarith)
    norm_num at h3
    linarith
  have := hreal h2 s.re hσ
  rw [← hsre] at this
  exact this hz.2

theorem proposition_at_iff : PrimePairExistsIffConditions := fun _ _ _ => Iff.rfl

lemma chi_eight_ne_one : chi8 ≠ 1 := by
  intro h
  have hp := chi_eight_primitive
  rw [isPrimitive_def, h, conductor_one] at hp
  norm_num at hp

lemma box_real {N : ℕ} [NeZero N] {Q : ℝ} (hQ : 0 ≤ Q) {χ : DirichletCharacter ℂ N} (h : ZeroFreeBox Q χ) (σ : ℝ)
    (hσ : 1 - 1 / 400 < σ) : LFunction χ (σ : ℂ) ≠ 0 :=
  h σ (by simpa using hσ) (by simpa using hQ)

theorem analytic_input_of_proposition : AnalyticInputsFromPNT := by
  intro hG hZ hP hRS hD hR hNR hNE
  obtain ⟨c₁, hc₁, hc₁', hNo⟩ := no_exceptional_zero_of_real hZ
  refine ⟨c₁ / 256, by positivity, fun ε A hε hA => ?_⟩
  obtain ⟨x1, hT⟩ := thin_of_no_exceptional_zero hP hRS hD hR ε c₁ hε hc₁ hc₁'
  obtain ⟨x2, hL⟩ := hNE ε A hε hA
  obtain ⟨x3, hO⟩ := thin_one_of hG ε (c₁ / 256) hε
  refine ⟨max (max x1 x2) x3, fun x hx C q d _ _ h25 => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨h8, h16, w1, w2, w3, w4, hs, hsp, g1, g2, g3, g4, g5, g6, v1, v2, v3⟩ := h25
  have hH := prime_congruence_conditions q d Fact.out Fact.out h8 h16 hs
  refine ⟨hH, fun e he => ⟨?_, (valuesIff_valid e q d hH x ε C).2 ⟨v1, v2, v3⟩⟩⟩
  refine (thin_iff e q d _ _).2 ⟨fun ψ hψ y hy => ?_, fun y hy => hO x hx3 y hy⟩
  have hX1 : 0 < X1 ε x := Real.exp_pos _
  have hX2 : 0 < X2 ε x := Real.exp_pos _
  have hQ1 : 0 ≤ 8 * X1 ε x := by positivity
  have hQ2 : 0 ≤ 8 * X1 ε x * X2 ε x := by positivity
  obtain ⟨-, ⟨hdvd, -⟩, hne⟩ := character_of_facts e q d hH ψ
  have hlq : Real.log (condOf e q d ψ) ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 := by
    have hup := (hL x hx2 (2 ^ e) q d Nat.one_le_two_pow he w1 w2 w3 w4).2.2.2.2
    rw [← modulus_formula e q d] at hup
    refine le_trans (Real.log_le_log ?_ ?_) hup
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (condOf e q d ψ))
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (hostN e q d))) hdvd
  refine hT x hx1 _ (chiOf e q d ψ) (hne hψ).1 (hNo _ _ ?_) hlq y hy
  intro hsq σ hσ
  rcases real_characters_input e q d hH ψ hsq with c | c | c | c | c | c | c | c
  · exact absurd c hψ
  · rw [(same_character_g _ _ _ _ c).2.2.2.1]
    by_cases h1 : σ < 1
    · exact hNR.2 σ (by linarith) h1
    · exact LFunction_ne_zero_of_one_le_re chi8 (Or.inl chi_eight_ne_one) (by simpa using not_lt.1 h1)
  · exact box_real hQ1 (zeroFreeBox_same c g1.2.2.2) σ hσ
  · exact box_real hQ1 (zeroFreeBox_same c g2.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g3.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g4.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g5.2.2.2) σ hσ
  · exact box_real hQ2 (zeroFreeBox_same c g6.2.2.2) σ hσ

theorem analytic_input_conditional : AnalyticInputsOfNoSmallRealZero :=
  analytic_input_of_proposition Formalism.ZF.gzPNT Formalism.ZeroFreeDirichlet.zFRDirichlet Formalism.ZeroFreeDirichlet.perron_formula_character Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character
    Formalism.ZeroFreeDirichlet.logDerivRegionChi Formalism.ZeroFreeDirichlet.l_log_deriv_right

end Formalism.LFunctionChainParameters.LBr2
