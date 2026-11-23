import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.TameInertiaTowers.TowerFieldFoundations

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois

namespace Decomp

theorem frob_pow_mk {M : Type} [Field M] [NumberField M] (p : ℕ)
    (Q : Ideal (𝓞 M)) [Q.LiesOver (span {(p : ℤ)})] (F : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (k : ℕ) (x : 𝓞 M) :
    Ideal.Quotient.mk Q ((F ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (p ^ k) := by
  have hn : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ),
      Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have key : ∀ y : 𝓞 M, Ideal.Quotient.mk Q (F • y) = Ideal.Quotient.mk Q y ^ p := by
    intro y
    rw [← map_pow, Ideal.Quotient.eq, ← hn]
    exact hF y
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ' F k, mul_smul, key, ih, ← pow_mul, ← pow_succ p k]

theorem stab_frob_pow {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∀ x : 𝓞 M, σ • x - (F ^ k) • x ∈ Q := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hund : span {(p : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
  have hQ0 : Q ≠ ⊥ := by
    intro hQ
    have h1 : (p : ℤ) ∈ Q.under ℤ := by
      rw [← hund]
      exact Ideal.mem_span_singleton_self _
    have h2 := Ideal.mem_comap.mp h1
    rw [hQ, Ideal.mem_bot] at h2
    exact hp.ne_zero (by simpa using h2)
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  letI : Field (𝓞 M ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  haveI : CharP (𝓞 M ⧸ Q) p := by
    refine ⟨fun n => ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk Q) n, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : (n : 𝓞 M) ∈ Q ↔ (n : ℤ) ∈ Q.under ℤ :=
      ⟨fun h => Ideal.mem_comap.mpr (by rwa [map_natCast]),
        fun h => by simpa using Ideal.mem_comap.mp h⟩
    rw [e1, ← hund, Ideal.mem_span_singleton]
    norm_cast
  letI : Algebra (ZMod p) (𝓞 M ⧸ Q) := ZMod.algebra _ p
  have hσQ : Q ≤ Q.comap (MulSemiringAction.toRingHom _ (𝓞 M) σ) := by
    intro y hy
    rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
    have hσ' : σ • Q = Q := MulAction.mem_stabilizer_iff.mp hσ
    rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
    exact hy
  let sb : (𝓞 M ⧸ Q) →+* (𝓞 M ⧸ Q) :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ (𝓞 M) σ) hσQ
  let sa : (𝓞 M ⧸ Q) →ₐ[ZMod p] (𝓞 M ⧸ Q) :=
    { sb with
      commutes' := fun c => by
        change sb (algebraMap (ZMod p) _ c) = algebraMap (ZMod p) _ c
        rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast] }
  obtain ⟨⟨n, hlt⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (𝓞 M ⧸ Q)).2 sa
  have hn' : FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ n = sa := hn
  have key : ∀ m : ℕ, ∀ y : 𝓞 M ⧸ Q,
      (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ m) y = y ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ' (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q)) m, AlgHom.mul_apply, ih,
        FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, ← pow_succ p m]
  refine ⟨n, fun x => ?_⟩
  rw [← Ideal.Quotient.eq]
  have h1 : sa (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q (σ • x) := rfl
  rw [← h1, ← hn', key, frob_pow_mk p Q F hF n x]

theorem stab_eq_inertia_mul {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∃ ρ : Gal(M/ℚ), (∀ x : 𝓞 M, ρ • x - x ∈ Q) ∧ σ = ρ * F ^ k := by
  obtain ⟨k, hk⟩ := stab_frob_pow p Q F σ hF hσ
  refine ⟨k, σ * (F ^ k)⁻¹, fun x => ?_, by simp⟩
  have hx := hk ((F ^ k)⁻¹ • x)
  rwa [smul_inv_smul, ← mul_smul] at hx

theorem mem_stab_of {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G)
    (I : Ideal S) (h : ∀ z : S, g • z ∈ I ↔ z ∈ I) : g ∈ MulAction.stabilizer G I := by
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h (g⁻¹ • z), smul_inv_smul]

theorem smul_mem_iff_of_stab {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]
    (g : G) (I : Ideal S) (hg : g ∈ MulAction.stabilizer G I) (z : S) : g • z ∈ I ↔ z ∈ I := by
  rw [MulAction.mem_stabilizer_iff] at hg
  conv_lhs => rw [← hg]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

section Host

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem restrict_smul (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (x : 𝓞 (hostE ζ a b)) :
    algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x := by
  ext
  first
    | exact hστ x
    | simpa using hστ x

theorem mem_P_iff (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (x : 𝓞 (hostE ζ a b)) : x ∈ P ↔ algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x ∈ Q := by
  rw [(Ideal.LiesOver.over : P = Q.under (𝓞 (hostE ζ a b)))] <;> exact Ideal.mem_comap

theorem stab_restrict (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) Q) :
    σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P := by
  apply mem_stab_of
  intro z
  rw [mem_P_iff P Q, mem_P_iff P Q, restrict_smul σ τ hστ, smul_mem_iff_of_stab τ Q hτ]

theorem frob_restrict (p : ℕ) (Q : Ideal (𝓞 L)) [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (hτ : IsArithFrobAt ℤ τ Q) :
    IsArithFrobAt ℤ σ P := by
  have hPQ : P.under ℤ = Q.under ℤ :=
    (Ideal.LiesOver.over : span {(p : ℤ)} = P.under ℤ).symm.trans
      (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ)
  intro x
  have h2 := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
  rw [mem_P_iff P Q, map_sub, map_pow, hPQ]
  convert h2 using 2
  exact restrict_smul σ τ hστ x

theorem hcl_at_one (e : ℕ) : hcl e 1 = 1 := QuotientGroup.mk_one _

theorem hcl_neg_one' (e : ℕ) : hcl e (-1) = 1 := by
  unfold hcl
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

theorem hPart_inertia (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] (ρ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hρ : ∀ x : 𝓞 (hostE ζ a b), ρ • x - x ∈ P) : (galE e ζ a b ρ).2 = 1 := by
  show hPart e ζ a b ρ = 1
  unfold hPart
  split_ifs with hex
  swap
  · rfl
  have hu := Classical.choose_spec hex
  generalize Classical.choose hex = u at hu ⊢
  obtain ⟨n, hn⟩ : ∃ n, (u : ZMod (2 ^ (e + 2))).val = n := ⟨_, rfl⟩
  rw [hn] at hu
  have hnu : ((n : ℕ) : ZMod (2 ^ (e + 2))) = u := by
    rw [← hn]
    exact ZMod.natCast_zmod_val _
  have hprim : IsPrimitiveRoot ζ (2 ^ (e + 2)) := h.1
  have hN1 : 1 ≤ 2 ^ (e + 2) := Nat.one_le_two_pow
  have hζN : ζ ^ (2 ^ (e + 2)) = 1 := hprim.pow_eq_one
  have hinv : ζ⁻¹ = ζ ^ (2 ^ (e + 2) - 1) := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_add_cancel hN1, hζN]
  have hζint : IsIntegral ℤ ζ := hprim.isIntegral (by positivity)
  have hζiint : IsIntegral ℤ ζ⁻¹ := by
    rw [hinv]
    exact hζint.pow _
  have hθint : IsIntegral ℤ (thE ζ a b) :=
    (isIntegral_algebraMap_iff (algebraMap (hostE ζ a b) L).injective).mp (hζint.add hζiint)
  obtain ⟨zz, hzz⟩ : ∃ z : 𝓞 L, (z : L) = ζ := ⟨⟨ζ, hζint⟩, rfl⟩
  obtain ⟨tt, htt⟩ : ∃ t : 𝓞 (hostE ζ a b), (t : hostE ζ a b) = thE ζ a b := ⟨⟨_, hθint⟩, rfl⟩
  have hth : ((thE ζ a b : hostE ζ a b) : L) = ζ + ζ⁻¹ := rfl
  have hmemQ : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) ∈ Q := (mem_P_iff P Q _).mp (hρ tt)
  have heq : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) =
      zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) := by
    ext1
    have e1 : ((algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) : 𝓞 L) : L) =
        ((ρ (tt : hostE ζ a b) : hostE ζ a b) : L) - ((tt : hostE ζ a b) : L) := by
      first
        | rfl
        | simp
    have e2 : ((zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) : 𝓞 L) : L) =
        (zz : L) ^ n + (zz : L) ^ ((2 ^ (e + 2) - 1) * n) - (zz : L) - (zz : L) ^ (2 ^ (e + 2) - 1) := by
      first
        | rfl
        | simp
    rw [e1, e2, htt, hth, hu, hzz, pow_mul, ← hinv]
    ring
  obtain ⟨zq, hzq⟩ : ∃ w, Ideal.Quotient.mk Q zz = w := ⟨_, rfl⟩
  have hrel : zq ^ n + zq ^ ((2 ^ (e + 2) - 1) * n) = zq + zq ^ (2 ^ (e + 2) - 1) := by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemQ
    rw [heq] at h0
    simp only [map_sub, map_add, map_pow, hzq] at h0
    linear_combination h0
  have hzzN : zz ^ (2 ^ (e + 2)) = 1 := by
    ext1
    have e3 : ((zz ^ (2 ^ (e + 2)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 2)) := by
      first
        | rfl
        | simp
    rw [e3, hzz, hζN]
    all_goals first | rfl | simp
  have hneg : ζ ^ (2 ^ (e + 1)) = -1 := by
    have hsq : ζ ^ (2 ^ (e + 1)) * ζ ^ (2 ^ (e + 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hζN
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exfalso
      have hdv := (hprim.pow_eq_one_iff_dvd _).mp h1
      have h4 := Nat.le_of_dvd (by positivity) hdv
      have hx : 0 < 2 ^ (e + 1) := by positivity
      have h5 : 2 ^ (e + 2) = 2 * 2 ^ (e + 1) := by ring
      omega
    · exact h1
  have hzzneg : zz ^ (2 ^ (e + 1)) = -1 := by
    ext1
    have e4 : ((zz ^ (2 ^ (e + 1)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 1)) := by
      first
        | rfl
        | simp
    rw [e4, hzz, hneg]
    all_goals first | rfl | simp
  have h2notQ : (2 : 𝓞 L) ∉ Q := by
    intro h2
    have h2' : (2 : ℤ) ∈ Q.under ℤ := Ideal.mem_comap.mpr (by simpa using h2)
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ), Ideal.mem_span_singleton] at h2'
    have h6 : p ∣ 2 := by exact_mod_cast h2'
    rcases Nat.prime_two.eq_one_or_self_of_dvd p h6 with h3 | h3
    · exact hp.one_lt.ne' h3
    · exact hp2 h3
  have hfin : zq ^ (2 ^ (e + 2)) = 1 := by
    rw [← hzq, ← map_pow, hzzN, map_one]
  have hnot : ¬ zq ^ (2 ^ (e + 1)) = 1 := by
    intro h1
    rw [← hzq, ← map_pow, hzzneg, map_neg, map_one] at h1
    apply h2notQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    have h7 : (2 : 𝓞 L ⧸ Q) = 1 - (-1) := by ring
    rw [h7, h1, sub_self]
  have horder : orderOf zq = 2 ^ (e + 2) := orderOf_eq_prime_pow hnot hfin
  have hpz : IsPrimitiveRoot zq (2 ^ (e + 2)) := horder ▸ IsPrimitiveRoot.orderOf zq
  have hCD : zq * zq ^ (2 ^ (e + 2) - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hN1, hfin]
  have hAB : zq ^ n * zq ^ ((2 ^ (e + 2) - 1) * n) = 1 := by
    rw [pow_mul, ← mul_pow, hCD, one_pow]
  have hkey : (zq ^ n * zq - 1) * (zq ^ n * zq ^ (2 ^ (e + 2) - 1) - 1) = 0 := by
    linear_combination (zq ^ n) * hrel - hAB + (zq ^ n) ^ 2 * hCD
  rcases mul_eq_zero.mp hkey with h1 | h1
  · have h1' : zq ^ (n + 1) = 1 := by
      rw [pow_succ]
      exact sub_eq_zero.mp h1
    have hd := (hpz.pow_eq_one_iff_dvd _).mp h1'
    have hc : ((n + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd
    have hu' : (u : ZMod (2 ^ (e + 2))) = -1 := by
      rw [← hnu]
      push_cast at hc
      linear_combination hc
    have hu1 : u = -1 := Units.ext (by rw [hu', Units.val_neg, Units.val_one])
    rw [hu1]
    exact hcl_neg_one' e
  · have h1' : zq ^ (n + (2 ^ (e + 2) - 1)) = 1 := by
      rw [pow_add]
      exact sub_eq_zero.mp h1
    have hd := (hpz.pow_eq_one_iff_dvd _).mp h1'
    have hc : ((n + (2 ^ (e + 2) - 1) : ℕ) : ZMod (2 ^ (e + 2))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd
    have hu' : (u : ZMod (2 ^ (e + 2))) = 1 := by
      rw [Nat.cast_add, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, hnu] at hc
      linear_combination hc
    have hu1 : u = 1 := Units.ext (by rw [hu', Units.val_one])
    rw [hu1]
    exact hcl_at_one e

end Host

section Two

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem two_mem {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M))
    [P.LiesOver (span {(2 : ℤ)})] : (2 : 𝓞 M) ∈ P := by
  have h2 : (2 : ℤ) ∈ P.under ℤ := by
    rw [← (Ideal.LiesOver.over : span {(2 : ℤ)} = P.under ℤ)]
    exact Ideal.mem_span_singleton_self 2
  simpa using Ideal.mem_comap.mp h2

theorem omega_integral {F : Type} [Field F] [NumberField F] {r : ℕ} (hr4 : r % 4 = 3) {X : F}
    (hX : X ^ 2 = -(r : F)) : IsIntegral ℤ ((1 + X) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r + 1 = 4 * m := ⟨(r + 1) / 4, by omega⟩
  have hm' : (r : F) + 1 = 4 * (m : F) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · simp
    linear_combination (1 / 4 : F) * hX - (1 / 4 : F) * hm'

theorem aE_sq_eq_neg_q (h : IsLayer (e + 2) q d ζ a b) :
    aE ζ a b ^ 2 = ((-(q : ℤ) : ℤ) : hostE ζ a b) := by
  apply Subtype.ext
  simp [aE, h.2.1]

theorem bE_sq' (h : IsLayer (e + 2) q d ζ a b) :
    bE ζ a b ^ 2 = ((-(d : ℤ) : ℤ) : hostE ζ a b) := by
  apply Subtype.ext
  simp [bE, h.2.2.1]

theorem stab_two_sgn (hqd : HypOdd q d) (hd16 : d % 16 = 7) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P) :
    (galE e ζ a b σ).1.2 = 1 := by
  have hbsq : bE ζ a b ^ 2 = -((d : ℕ) : hostE ζ a b) := by simpa using bE_sq' h
  have hfix : σ (bE ζ a b) = bE ζ a b := by
    by_contra hne
    have hsq : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
      rw [← map_pow, hbsq, map_neg, map_natCast]
    have hσb : σ (bE ζ a b) = -(bE ζ a b) := by
      have hm0 : (σ (bE ζ a b) - bE ζ a b) * (σ (bE ζ a b) + bE ζ a b) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hm0 with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hne
      · exact eq_neg_of_add_eq_zero_left h1
    have hint : IsIntegral ℤ ((1 + bE ζ a b) / 2) := omega_integral (by omega) hbsq
    obtain ⟨ω, hωv⟩ : ∃ ω : 𝓞 (hostE ζ a b), (ω : hostE ζ a b) = (1 + bE ζ a b) / 2 :=
      ⟨⟨_, hint⟩, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m2 : ℕ, d + 1 = 8 * m2 := ⟨(d + 1) / 8, by omega⟩
    have hm : (d : hostE ζ a b) + 1 = 8 * (m2 : hostE ζ a b) := by exact_mod_cast hm2
    have hprod : ω * (1 - ω) = 2 * (m2 : 𝓞 (hostE ζ a b)) := by
      ext1
      have e3 : ((ω * (1 - ω) : 𝓞 (hostE ζ a b)) : hostE ζ a b) =
          (ω : hostE ζ a b) * (1 - (ω : hostE ζ a b)) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      have e4 : ((2 * (m2 : 𝓞 (hostE ζ a b)) : 𝓞 (hostE ζ a b)) : hostE ζ a b) =
          2 * (m2 : hostE ζ a b) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      rw [e3, e4, hωv]
      have hb2 : bE ζ a b ^ 2 = 1 - 8 * (m2 : hostE ζ a b) := by
        rw [hbsq, ← hm]
        ring
      linear_combination (-1 / 4 : hostE ζ a b) * hb2
    have hsw : σ • ω = 1 - ω := by
      ext
      have e1 : ((σ • ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = σ (ω : hostE ζ a b) := by
        first
          | rfl
          | simp
      have e2 : ((1 - ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = 1 - (ω : hostE ζ a b) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      rw [e1, e2, hωv, map_div₀, map_add, map_one, hσb, map_ofNat]
      ring
    have hsmul : ∀ z, σ • z ∈ P ↔ z ∈ P := smul_mem_iff_of_stab σ P hσ
    have hprodP : ω * (1 - ω) ∈ P := by
      rw [hprod]
      exact Ideal.mul_mem_right _ _ (two_mem P)
    have hboth : ω ∈ P ∧ 1 - ω ∈ P := by
      rcases (inferInstance : P.IsPrime).mem_or_mem hprodP with h1 | h1
      · exact ⟨h1, by rw [← hsw]; exact (hsmul ω).mpr h1⟩
      · refine ⟨?_, h1⟩
        have h3 := (hsmul (1 - ω)).mpr h1
        rwa [smul_sub, smul_one, hsw, sub_sub_cancel] at h3
    have h1P : (1 : 𝓞 (hostE ζ a b)) ∈ P := by
      simpa using P.add_mem hboth.1 hboth.2
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one P).mpr h1P)
  show sgn σ (bE ζ a b) = 1
  unfold sgn
  exact if_pos hfix

end Two

end Decomp

open Decomp

theorem hostDecomp : HostDecomp := by
  intro e q d hH L _ _ ζ a b h uq ud huq hud σ
  have hqd := hH.toHypOdd
  have hQD := hH.toHypQD
  have hrec := hostRecip q d hH
  obtain ⟨hq, hd, -, hd16, hjac⟩ := hH
  have hq2 : q ≠ 2 := hqd.2.2.2.1
  have hd2 : d ≠ 2 := hqd.2.2.2.2
  have hqd' : q ≠ d := hqd.2.2.1
  obtain ⟨hLgal, -, hmulL, hbijL⟩ := layer_galois hqd h
  have := hLgal
  obtain ⟨hEgal, -, hmulE, hbijE⟩ := hostGalois e q d hqd L ζ a b h
  have := hEgal
  let gE : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) →* GG e := MonoidHom.mk' (galE e ζ a b) hmulE
  let gL : Gal(L/ℚ) →* GalL (e + 2) := MonoidHom.mk' (galMap h.1 a b) hmulL
  have hpowE : ∀ (x : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ),
      galE e ζ a b (x ^ k) = galE e ζ a b x ^ k := fun x k => map_pow gE x k
  have hpowL : ∀ (x : Gal(L/ℚ)) (k : ℕ), galMap h.1 a b (x ^ k) = galMap h.1 a b x ^ k :=
    fun x k => map_pow gL x k
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have hqnd : ¬ q ∣ d := fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv)
  have hdnq : ¬ d ∣ q := fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm
  have hIT := layerInertiaTame (e + 2) q d (by omega) hqd L ζ a b h
  refine ⟨fun P _ _ => ?_, fun P _ _ => ?_, fun P _ _ => ?_⟩
  ·
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(2 : ℤ)}) := Ideal.LiesOver.trans Q P (span {(2 : ℤ)})
    rw [mem_Psi_iff]
    refine ⟨stab_two_sgn hqd hd16 h P σ, fun hs => ?_⟩
    obtain ⟨τ, hστ⟩ := exists_lift hqd h σ
    have hgl := galE_lift h hστ
    apply stab_restrict P Q σ τ hστ
    rw [layerDecompTwo (e + 2) q d (by omega) hQD L ζ a b h Q τ, D2, MonoidHom.mem_ker]
    have h1 := congrArg (fun g : GG e => g.1.2) hgl
    simp only at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_snd]
    rw [← h1]
    exact hs
  ·
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(q : ℤ)}) := Ideal.LiesOver.trans Q P (span {(q : ℤ)})
    have : Finite (𝓞 L ⧸ Q) := by
      have hpb : span {(q : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero
      exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
    obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
    obtain ⟨σF, hσF⟩ := exists_restrict hqd h F
    have hFE : IsArithFrobAt ℤ σF P := frob_restrict q Q P σF F hσF hF
    have hF1 : (galMap h.1 a b F).1 = uq := Units.ext ((odd_cyc_frob h.1 q hq2 Q F hF).trans huq.symm)
    have hF3 : (galMap h.1 a b F).2.2 = 1 := by
      have := odd_frob_sgn q hq2 Q F hF b _ hb
        (by rw [dvd_neg]; intro h'; exact hqnd (by exact_mod_cast h'))
      rw [hjac] at this
      exact Units.ext this
    have hgF : galE e ζ a b σF = (((galMap h.1 a b F).2.1, 1), hcl e uq) := by
      rw [galE_lift h hσF, hF3, hF1]
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul q P σF σ hFE hσ
      have e2 : (galE e ζ a b ρ).2 = 1 := hPart_inertia hqd h q hq hq2 Q P ρ hρ
      have e1 : (galE e ζ a b ρ).1.2 = 1 :=
        odd_sgn_inertia q hq hq2 P ρ hρ (bE ζ a b) d (bE_sq' h) hqnd
      rw [hmulE, hpowE, hgF]
      refine ⟨?_, k, ?_⟩
      · simp [e1]
      · simp [e2]
    · rintro ⟨hs2, k, hk⟩
      set s' : ℤˣ := (galE e ζ a b σ).1.1 * ((galMap h.1 a b F).2.1 ^ k)⁻¹ with hs'
      obtain ⟨ι, hι⟩ := hbijL.2 ((1, s', 1) : GalL (e + 2))
      have hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q := by
        rw [hIT.1 Q ι, odd_mem_Iq, hι]
        rcases Int.units_eq_one_or s' with hs | hs <;> rw [hs]
        · left; rfl
        · right; rfl
      have hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q :=
        Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q
          (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)
      obtain ⟨σ', hσ'⟩ := exists_restrict hqd h (ι * F ^ k)
      have hgm : galMap h.1 a b (ι * F ^ k) =
          ((galMap h.1 a b F).1 ^ k, s' * (galMap h.1 a b F).2.1 ^ k, 1) := by
        rw [hmulL, hpowL, hι]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF3]
      have hσσ : σ' = σ := by
        apply hbijE.1
        rw [galE_lift h hσ', hgm, hF1]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · rw [hs', inv_mul_cancel_right]
        · exact hs2.symm
        · rw [hk]; exact QuotientGroup.mk_pow _ uq k
      rw [← hσσ]
      exact stab_restrict P Q σ' _ hσ' hτ
  ·
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(d : ℤ)}) := Ideal.LiesOver.trans Q P (span {(d : ℤ)})
    have : Finite (𝓞 L ⧸ Q) := by
      have hpb : span {(d : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hd.ne_zero
      exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
    obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
    obtain ⟨σF, hσF⟩ := exists_restrict hqd h F
    have hFE : IsArithFrobAt ℤ σF P := frob_restrict d Q P σF F hσF hF
    have hF1 : (galMap h.1 a b F).1 = ud := Units.ext ((odd_cyc_frob h.1 d hd2 Q F hF).trans hud.symm)
    have hF2 : (galMap h.1 a b F).2.1 = -1 := by
      have := odd_frob_sgn d hd2 Q F hF a _ ha
        (by rw [dvd_neg]; intro h'; exact hdnq (by exact_mod_cast h'))
      rw [hrec] at this
      exact Units.ext this
    have hgF : galE e ζ a b σF = ((-1, (galMap h.1 a b F).2.2), hcl e ud) := by
      rw [galE_lift h hσF, hF2, hF1]
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul d P σF σ hFE hσ
      have e2 : (galE e ζ a b ρ).2 = 1 := hPart_inertia hqd h d hd hd2 Q P ρ hρ
      have e1 : (galE e ζ a b ρ).1.1 = 1 :=
        odd_sgn_inertia d hd hd2 P ρ hρ (aE ζ a b) q (aE_sq_eq_neg_q h) hdnq
      rw [hmulE, hpowE, hgF]
      refine ⟨k, ?_, ?_⟩
      · simp [e1]
      · simp [e2]
    · rintro ⟨k, hk1, hk2⟩
      set t' : ℤˣ := (galE e ζ a b σ).1.2 * ((galMap h.1 a b F).2.2 ^ k)⁻¹ with ht'
      obtain ⟨ι, hι⟩ := hbijL.2 ((1, 1, t') : GalL (e + 2))
      have hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q := by
        rw [hIT.2 Q ι, odd_mem_Id, hι]
        rcases Int.units_eq_one_or t' with ht | ht <;> rw [ht]
        · left; rfl
        · right; rfl
      have hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q :=
        Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q
          (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)
      obtain ⟨σ', hσ'⟩ := exists_restrict hqd h (ι * F ^ k)
      have hgm : galMap h.1 a b (ι * F ^ k) =
          ((galMap h.1 a b F).1 ^ k, (-1) ^ k, t' * (galMap h.1 a b F).2.2 ^ k) := by
        rw [hmulL, hpowL, hι]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF2]
      have hσσ : σ' = σ := by
        apply hbijE.1
        rw [galE_lift h hσ', hgm, hF1]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · exact hk1.symm
        · rw [ht', inv_mul_cancel_right]
        · rw [hk2]; exact QuotientGroup.mk_pow _ ud k
      rw [← hσσ]
      exact stab_restrict P Q σ' _ hσ' hτ

theorem hostDecompConj : HostDecompConj := by
  intro e q d hyp L _ _ ζ a b h σ hσ p hp P _ _
  have hm1 : (-1 : ℤˣ) ≠ 1 := by
    intro h1
    have h2 := congrArg Units.val h1
    simp at h2
  have hq8 : q % 8 = 3 := hyp.2.2.1
  have hd16 : d % 16 = 7 := hyp.2.2.2.1
  have hcq : Nat.Coprime q (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.1 Nat.prime_two).mpr (by omega))
  have hcd : Nat.Coprime d (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.2.1 Nat.prime_two).mpr (by omega))
  have HD := hostDecomp e q d hyp L ζ a b h (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd)
    (ZMod.coe_unitOfCoprime q hcq) (ZMod.coe_unitOfCoprime d hcd) σ
  rw [hσ] at HD
  have hnotPsi : cc e ∉ Psi e := by
    intro hmem
    have h3 : chD e (cc e) = -1 := by
      first
        | rfl
        | simp [chD, cc, c0]
    exact hm1 (h3.symm.trans (MonoidHom.mem_ker.mp hmem))
  rcases hp with rfl | rfl | ⟨rfl, he2⟩
  · haveI : P.LiesOver (span {(2 : ℤ)}) := by
      have h' : P.LiesOver (span {((2 : ℕ) : ℤ)}) := inferInstance
      simpa using h'
    rw [HD.1 P]
    exact hnotPsi
  · rw [HD.2.1 P]
    rintro ⟨h1, -⟩
    exact hm1 h1
  · rw [HD.2.2 P]
    rintro ⟨k, hk1, hk2⟩
    have hk1' : (-1 : ℤˣ) = (-1) ^ k := hk1
    obtain ⟨j, rfl⟩ : Odd k := by
      rcases Nat.even_or_odd k with hev | hod
      · rw [hev.neg_one_pow] at hk1'
        exact absurd hk1' hm1
      · exact hod
    have hk3 : ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk2.symm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hk3
    obtain ⟨i, hi⟩ := hk3
    have hpm : (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = 1 ∨
        (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = -1 := by
      rw [← hi]
      rcases Int.even_or_odd i with hev | hod
      · left
        exact hev.neg_one_zpow
      · right
        exact hod.neg_one_zpow
    have h16 : 16 ∣ 2 ^ (e + 2) := by
      have h4 := Nat.pow_dvd_pow 2 (show 4 ≤ e + 2 by omega)
      simpa using h4
    have hd7 : ((p : ℕ) : ZMod 16) = 7 := by
      rw [← ZMod.natCast_mod, hd16]
      all_goals first | rfl | decide
    have h49 : (7 : ZMod 16) ^ 2 = 1 := by decide
    have h7 : (7 : ZMod 16) ^ (2 * j + 1) = 7 := by
      rw [pow_succ, pow_mul, h49, one_pow, one_mul]
    have hval : ZMod.castHom h16 (ZMod 16)
        ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 7 := by
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, map_pow, map_natCast, hd7, h7]
    rcases hpm with h1 | h1
    · rw [h1, Units.val_one, map_one] at hval
      exact absurd hval (by decide)
    · rw [h1, Units.val_neg, Units.val_one, map_neg, map_one] at hval
      exact absurd hval (by decide)

theorem hostDecompBoth : HostDecomp ∧ HostDecompConj := ⟨hostDecomp, hostDecompConj⟩

end Formalism.FrobeniusOrbits
