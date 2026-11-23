import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EqOfPowEqOne

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

namespace D7

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section Field

variable {e q d : ℕ} (hH : HostHyp q d) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (e + 2) q d ζ a b)
include hH h

theorem frob_art (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 2 ^ (e + 2) * q * d)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)) = (p : ZMod (2 ^ (e + 2) * q * d))) :
    IsArithFrobAt ℤ σ P ↔ galE e ζ a b σ = art0 e hH u := by
  have hpp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hp (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _)
  have hpq : p ≠ q := by
    rintro rfl
    exact hp (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have hpd : p ≠ d := by
    rintro rfl
    exact hp (dvd_mul_left _ _)
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have hpodd : Odd p := hpp.odd_of_ne_two hp2
  have recip : ∀ r : ℕ, r % 4 = 3 → jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by
    intro r hr
    rw [jacobiSym.neg _ hpodd]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd) with h4 | h4
    · rw [ZMod.χ₄_nat_one_mod_four h4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four h4 (Nat.odd_iff.mpr (by omega))]
    · rw [ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hr h4,
        neg_one_mul, neg_neg]
  have huN : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD 2 ^ (e + 2) * q * d] := by
    rw [hu, ZMod.val_natCast]
    exact Nat.mod_modEq p _
  have huq : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD q] :=
    (Nat.ModEq.of_mul_right d huN).of_mul_left (2 ^ (e + 2))
  have hud : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD d] :=
    Nat.ModEq.of_mul_left (2 ^ (e + 2) * q) huN
  have hu2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD 2 ^ (e + 2)] :=
    (Nat.ModEq.of_mul_right d huN).of_mul_right q
  have hcop : p.Coprime (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
  have hvp : ((ZMod.unitOfCoprime p hcop : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = (p : ZMod (2 ^ (e + 2))) :=
    ZMod.coe_unitOfCoprime p hcop
  have hA : (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (p : ℤ) q := by
    apply artinMap_first_eq_jacobiSym_of_modEq
    exact huq
  have hB : (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (p : ℤ) d := by
    apply artinMap_second_eq_jacobiSym_of_modEq
    exact hud
  have hC : (art0 e hH u).2 = hcl e (ZMod.unitOfCoprime p hcop) := by
    exact artinMap_dyadic_eq_of_modEq (hu := hu2) (hv := hvp) ..
  rw [(Formalism.FrobeniusOrbits.Final.host_field.2.2.2.2.2.2.2.2.2.2.2.1 e q d hH.toHypOdd L ζ a b h p hp2 hpq hpd P).2.1 σ]
  constructor
  · rintro ⟨h1, h2, v', hv', h3⟩
    have hvv : v' = ZMod.unitOfCoprime p hcop := Units.ext (hv'.trans hvp.symm)
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact Units.ext (h1.trans ((recip q hq4).trans hA.symm))
    · exact Units.ext (h2.trans ((recip d hd4).trans hB.symm))
    · rw [h3, hvv, hC]
  · intro hg
    refine ⟨?_, ?_, ZMod.unitOfCoprime p hcop, hvp, ?_⟩
    · rw [hg, hA]
      exact (recip q hq4).symm
    · rw [hg, hB]
      exact (recip d hd4).symm
    · rw [hg, hC]

theorem inertia_art (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD ordCompl[l] (2 ^ (e + 2) * q * d)] ∧
        galE e ζ a b σ = art0 e hH u := by
  have hI := Formalism.FrobeniusOrbits.Final.host_field.2.2.2.2.2.2.2.2.2.2.2.2.1 e q d hH L ζ a b h σ
  by_cases hl2 : l = 2
  · subst hl2
    haveI : P.LiesOver (span {(2 : ℤ)}) := by
      simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
    rw [hI.1 P, ordCompl_two (hH := hH)]
    exact inertia_two ..
  by_cases hlq : l = q
  · subst hlq
    rw [hI.2.1 P, ordCompl_q (hH := hH)]
    exact inertia_q ..
  by_cases hld : l = d
  · subst hld
    rw [hI.2.2 P, ordCompl_d (hH := hH)]
    exact inertia_d ..
  have hlp : l.Prime := Fact.out
  have hqp : q.Prime := hH.1
  have hdp : d.Prime := hH.2.1
  have hN0 : 2 ^ (e + 2) * q * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hqp.ne_zero) hdp.ne_zero
  have hnd : ¬ l ∣ 2 ^ (e + 2) * q * d := by
    intro hdv
    rcases (Nat.Prime.dvd_mul hlp).mp hdv with h1 | h1
    · rcases (Nat.Prime.dvd_mul hlp).mp h1 with h2 | h2
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).mp (hlp.dvd_of_dvd_pow h2))
      · exact hlq ((Nat.prime_dvd_prime_iff_eq hlp hqp).mp h2)
    · exact hld ((Nat.prime_dvd_prime_iff_eq hlp hdp).mp h1)
  have hoc : ordCompl[l] (2 ^ (e + 2) * q * d) = 2 ^ (e + 2) * q * d := by
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero, Nat.div_one]
  rw [hoc, (Formalism.FrobeniusOrbits.Final.host_field.2.2.2.2.2.2.2.2.2.2.2.1 e q d hH.toHypOdd L ζ a b h l hl2 hlq hld P).2.2 σ]
  have hone : galE e ζ a b 1 = 1 := map_one (galEquiv hH.toHypOdd h)
  constructor
  · rintro rfl
    refine ⟨1, ?_, ?_⟩
    · rw [Units.val_one, ZMod.val_one_eq_one_mod]
      exact Nat.mod_modEq 1 _
    · rw [hone, map_one]
  · rintro ⟨u, hu1, hu2⟩
    haveI : NeZero (2 ^ (e + 2) * q * d) := ⟨hN0⟩
    have hu : u = 1 := by
      apply Units.ext
      rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod (2 ^ (e + 2) * q * d)), ← Nat.cast_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu1
    rw [hu, map_one, ← hone] at hu2
    exact (galEquiv hH.toHypOdd h).injective
      (show galEquiv hH.toHypOdd h σ = galEquiv hH.toHypOdd h 1 from hu2)

theorem decomp_art (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    σ ∈ MulAction.stabilizer _ P ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ l ^ k [MOD ordCompl[l] (2 ^ (e + 2) * q * d)] ∧
        galE e ζ a b σ = art0 e hH u := by
  have hl : l.Prime := Fact.out
  have hD := hostDecomp e q d hH L ζ a b h (ZMod.unitOfCoprime q (cop_2q e hH).symm)
    (ZMod.unitOfCoprime d (cop_2d e hH).symm) (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _) σ
  by_cases hN : l ∣ 2 ^ (e + 2) * q * d
  · rcases (dvd_N_iff e hH hl).mp hN with h2 | h2 | h2
    · subst h2
      have : P.LiesOver (span {(2 : ℤ)}) := ‹P.LiesOver (span {((2 : ℕ) : ℤ)})›
      rw [ordCompl_two e hH, hD.1 P, mem_Psi_iff, decomp_two e hH]
    · subst h2
      rw [ordCompl_q e hH, hD.2.1 P, decomp_q e hH _ (ZMod.coe_unitOfCoprime _ _)]
    · subst h2
      rw [ordCompl_d e hH, hD.2.2 P, decomp_d e hH _ (ZMod.coe_unitOfCoprime _ _)]
  · have := neZeroN e hH
    rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hl).mpr (Or.inr hN)]
    have hc : Nat.Coprime l (2 ^ (e + 2) * q * d) := (Nat.Prime.coprime_iff_not_dvd hl).mpr hN
    have hN' := hN
    rw [dvd_N_iff e hH hl, not_or, not_or] at hN'
    obtain ⟨⟨F, hF⟩, -, hin⟩ := Final.frob e q d hH.toHypOdd L ζ a b h l hN'.1 hN'.2.1 hN'.2.2 P
    set w := ZMod.unitOfCoprime l hc with hw
    have hwv : ∀ k : ℕ, ((w ^ k : (ZMod (2 ^ (e + 2) * q * d))ˣ) : ZMod (2 ^ (e + 2) * q * d)) =
        ((l ^ k : ℕ) : ZMod (2 ^ (e + 2) * q * d)) := fun k => by
      rw [Units.val_pow_eq_pow_val, hw, ZMod.coe_unitOfCoprime, Nat.cast_pow]
    have hFw := (frob_art hH h l hN P F w (ZMod.coe_unitOfCoprime _ _)).mp hF
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, hk⟩ := Decomp.stab_eq_inertia_mul l P F σ hF hσ
      refine ⟨w ^ k, k, ?_, ?_⟩
      · rw [hwv, ZMod.val_natCast]
        exact Nat.mod_modEq _ _
      · rw [hk, (hin ρ).mp hρ, one_mul, galE_pow hH.toHypOdd h, hFw, map_pow]
    · rintro ⟨u, k, hu, h1⟩
      have h2 : u = w ^ k := by
        apply Units.ext
        rw [hwv, ← ZMod.natCast_zmod_val (u : ZMod (2 ^ (e + 2) * q * d)), (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu]
      have h3 : σ = F ^ k := by
        apply galE_injective (e := e) hH.toHypOdd h
        rw [h1, h2, galE_pow hH.toHypOdd h, hFw, map_pow]
      rw [h3]
      exact Subgroup.pow_mem _ hF.mem_stabilizer k

omit hH h in
theorem frob_iff_inertia (P : Ideal (𝓞 (hostE ζ a b))) (F σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hF : IsArithFrobAt ℤ F P) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : 𝓞 (hostE ζ a b), (σ * F⁻¹) • x - x ∈ P := by
  have hF' : ∀ x : 𝓞 (hostE ζ a b), F • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hF
  have key : ∀ y : 𝓞 (hostE ζ a b), (σ * F⁻¹) • (F • y) = σ • y := by
    intro y
    rw [mul_smul, inv_smul_smul]
  show (∀ x : 𝓞 (hostE ζ a b), σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P) ↔ _
  constructor
  · intro hσ x
    obtain ⟨y, rfl⟩ : ∃ y, F • y = x := ⟨F⁻¹ • x, smul_inv_smul F x⟩
    rw [key]
    have h3 := P.sub_mem (hσ y) (hF' y)
    rwa [sub_sub_sub_cancel_right] at h3
  · intro hin y
    have h3 := P.add_mem (hin (F • y)) (hF' y)
    rwa [key, sub_add_sub_cancel] at h3

theorem exists_frob_lift (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    [P.LiesOver (span {(l : ℤ)})] :
    ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (span {(l : ℤ)})) (F : L ≃ₐ[ℚ] L)
      (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ F Q ∧ IsArithFrobAt ℤ σ P ∧
      galE e ζ a b σ = (((galMap h.1 a b F).2.1, (galMap h.1 a b F).2.2), hcl e (galMap h.1 a b F).1) := by
  have hl : l.Prime := Fact.out
  have hqd := hH.toHypOdd
  obtain ⟨hLgal, -⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have hQ : Q.LiesOver (span {(l : ℤ)}) := Ideal.LiesOver.trans Q P (span {(l : ℤ)})
  have : Finite (𝓞 L ⧸ Q) := by
    have hpb : span {(l : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
  obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
  obtain ⟨σ, hσ⟩ := Galois.exists_restrict hqd h F
  exact ⟨Q, hQp, hQ, F, σ, hF, Decomp.frob_restrict l Q P σ F hσ hF, galE_of_lift h hσ⟩

theorem exists_frob_art (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    [P.LiesOver (span {(l : ℤ)})] :
    ∃ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ), IsArithFrobAt ℤ σ P ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ l [MOD ordCompl[l] (2 ^ (e + 2) * q * d)] ∧
        galE e ζ a b σ = art0 e hH u := by
  have hl : l.Prime := Fact.out
  have hqd := hH.toHypOdd
  obtain ⟨Q, _, _, F, σ, hF, hσ, hg⟩ := exists_frob_lift hH h l P
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have hqnd : ¬ q ∣ d := (Nat.Prime.coprime_iff_not_dvd hH.1).mp (cop_qd hH)
  have hdnq : ¬ d ∣ q := (Nat.Prime.coprime_iff_not_dvd hH.2.1).mp (cop_qd hH).symm
  by_cases hN : l ∣ 2 ^ (e + 2) * q * d
  · rcases (dvd_N_iff e hH hl).mp hN with h2 | h2 | h2
    · subst h2
      have : P.LiesOver (span {(2 : ℤ)}) := ‹P.LiesOver (span {((2 : ℕ) : ℤ)})›
      have hD := fun τ => (hostDecomp e q d hH L ζ a b h (ZMod.unitOfCoprime q (cop_2q e hH).symm)
        (ZMod.unitOfCoprime d (cop_2d e hH).symm) (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _) τ).1 P
      have h1 : (galE e ζ a b σ).1.2 = 1 := (hD σ).mp hσ.mem_stabilizer
      have h3 : (galE e ζ a b σ).1.1 = -1 := by
        refine (Int.units_eq_one_or _).resolve_left fun h4 => ?_
        obtain ⟨s, hs⟩ := exists_galE_eq hqd h (sg e)
        obtain ⟨k, ρ, hρ, hk⟩ := Decomp.stab_eq_inertia_mul 2 P σ s hσ ((hD s).mpr (by rw [hs]; rfl))
        have h5 := ((hostInertia e q d hH L ζ a b h ρ).1 P).mp hρ
        have h6 : (galE e ζ a b σ).1 = 1 := Prod.ext h4 h1
        have h7 := congrArg (fun g : FrobeniusOrbits.GG e => g.1) hs
        simp only [hk, galE_mul hqd h, galE_pow hqd h, Prod.fst_mul, Prod.pow_fst, h5, h6, one_pow, mul_one] at h7
        exact absurd h7 (show ¬ (1 : G0) = (-1, 1) by decide)
      obtain ⟨x, v, hv, hx⟩ := exists_rep e (galE e ζ a b σ).2
      obtain ⟨u, -, u2, u3, hu⟩ := exists_art e hH _ x 2 2 v hv hx (by rw [h3, jac_2q hH]; rfl)
        (by rw [h1, jac_2d hH]; rfl)
      exact ⟨σ, u, hσ, by
        rw [ordCompl_two e hH]; exact (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨u2, u3⟩, hu⟩
    · subst h2
      have h1 := odd_cyc_frob h.1 l hqd.2.2.2.1 Q F hF
      have h3 := odd_frob_sgn l hqd.2.2.2.1 Q F hF b _ hb
        (by rw [dvd_neg]; intro h'; exact hqnd (by exact_mod_cast h'))
      rw [hH.2.2.2.2] at h3
      obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) (galE e ζ a b σ).1.1
      obtain ⟨u, u1, -, u3, hu⟩ := exists_art e hH (galE e ζ a b σ) l y l _ h1 (by rw [hg]; rfl) hy.symm
        (by rw [jac_qd hH, hg]; exact h3)
      exact ⟨σ, u, hσ, by
        rw [ordCompl_q e hH]; exact (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨u1, u3⟩, hu⟩
    · subst h2
      have h1 := odd_cyc_frob h.1 l hqd.2.2.2.2 Q F hF
      have h3 := odd_frob_sgn l hqd.2.2.2.2 Q F hF a _ ha
        (by rw [dvd_neg]; intro h'; exact hdnq (by exact_mod_cast h'))
      rw [hostRecip q l hH] at h3
      obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) (galE e ζ a b σ).1.2
      obtain ⟨u, u1, u2, -, hu⟩ := exists_art e hH (galE e ζ a b σ) l l z _ h1 (by rw [hg]; rfl)
        (by rw [jac_dq hH, hg]; exact h3) hz.symm
      exact ⟨σ, u, hσ, by
        rw [ordCompl_d e hH]; exact (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨u1, u2⟩, hu⟩
  · have := neZeroN e hH
    have hc : Nat.Coprime l (2 ^ (e + 2) * q * d) := (Nat.Prime.coprime_iff_not_dvd hl).mpr hN
    refine ⟨σ, ZMod.unitOfCoprime l hc, hσ, ?_, (frob_art hH h l hN P σ _ (ZMod.coe_unitOfCoprime _ _)).mp hσ⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact (Nat.mod_modEq _ _).of_dvd (Nat.ordCompl_dvd _ _)

theorem frob_any_art (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    IsArithFrobAt ℤ σ P ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ l [MOD ordCompl[l] (2 ^ (e + 2) * q * d)] ∧
        galE e ζ a b σ = art0 e hH u := by
  obtain ⟨F, u0, hF, hu0, hgF⟩ := exists_frob_art hH h l P
  rw [frob_iff_inertia P F σ hF, inertia_art hH h l P]
  have hmul : ∀ τ₁ τ₂ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      galE e ζ a b (τ₁ * τ₂) = galE e ζ a b τ₁ * galE e ζ a b τ₂ :=
    fun τ₁ τ₂ => map_mul (galEquiv hH.toHypOdd h) τ₁ τ₂
  have hinv : ∀ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b τ⁻¹ = (galE e ζ a b τ)⁻¹ :=
    fun τ => map_inv (galEquiv hH.toHypOdd h) τ
  have hN0 : 2 ^ (e + 2) * q * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hH.1.ne_zero) hH.2.1.ne_zero
  haveI : NeZero (2 ^ (e + 2) * q * d) := ⟨hN0⟩
  have hdvd : ordCompl[l] (2 ^ (e + 2) * q * d) ∣ 2 ^ (e + 2) * q * d := Nat.ordCompl_dvd _ _
  have hval : ∀ x y : (ZMod (2 ^ (e + 2) * q * d))ˣ,
      ((x * y : (ZMod (2 ^ (e + 2) * q * d))ˣ) : ZMod (2 ^ (e + 2) * q * d)).val ≡
        (x : ZMod (2 ^ (e + 2) * q * d)).val * (y : ZMod (2 ^ (e + 2) * q * d)).val
        [MOD ordCompl[l] (2 ^ (e + 2) * q * d)] := by
    intro x y
    rw [Units.val_mul, ZMod.val_mul]
    exact Nat.ModEq.of_dvd hdvd (Nat.mod_modEq _ _)
  constructor
  · rintro ⟨u1, hu1, hg1⟩
    refine ⟨u1 * u0, ?_, ?_⟩
    · have := (hval u1 u0).trans (Nat.ModEq.mul hu1 hu0)
      rwa [one_mul] at this
    · rw [map_mul, ← hgF, ← hg1, hmul, hinv, inv_mul_cancel_right]
  · rintro ⟨u, hu, hg⟩
    refine ⟨u * u0⁻¹, ?_, ?_⟩
    · have h1 : ((u0⁻¹ * u0 : (ZMod (2 ^ (e + 2) * q * d))ˣ) : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1
          [MOD ordCompl[l] (2 ^ (e + 2) * q * d)] := by
        rw [inv_mul_cancel, Units.val_one, ZMod.val_one_eq_one_mod]
        exact Nat.ModEq.of_dvd hdvd (Nat.mod_modEq 1 _)
      have h2 := (hval u0⁻¹ u0).symm.trans h1
      have h3 := (hval u u0⁻¹).trans (Nat.ModEq.mul_right _ (hu.trans hu0.symm))
      have hc : (u0 : ZMod (2 ^ (e + 2) * q * d)).val * ((u0⁻¹ : (ZMod (2 ^ (e + 2) * q * d))ˣ) : ZMod (2 ^ (e + 2) * q * d)).val =
          ((u0⁻¹ : (ZMod (2 ^ (e + 2) * q * d))ˣ) : ZMod (2 ^ (e + 2) * q * d)).val * (u0 : ZMod (2 ^ (e + 2) * q * d)).val :=
        Nat.mul_comm _ _
      rw [hc] at h3
      exact h3.trans h2
    · rw [hmul, hinv, hg, hgF, map_mul, map_inv]

omit h in
theorem exact_art (he : 1 ≤ e) : ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2) * q * d / 2] ∧ art0 e hH u ≠ 1 := by
  have hqp : q.Prime := hH.1
  have hdp : d.Prime := hH.2.1
  have hq8 := hH.2.2.1
  have hd16 := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hA1 : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
  have hA2 : 2 ^ (e + 2) = 4 * 2 ^ e := by ring
  have hA0 : 2 ≤ 2 ^ e := by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) he
  have hcop : (1 + 2 ^ (e + 1)).Coprime (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)))
  obtain ⟨v, hv⟩ : ∃ v : (ZMod (2 ^ (e + 2)))ˣ,
      (v : ZMod (2 ^ (e + 2))) = ((1 + 2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 2))) :=
    ⟨ZMod.unitOfCoprime _ hcop, ZMod.coe_unitOfCoprime _ hcop⟩
  have hvne : hcl e v ≠ 1 := by
    intro hc
    have hmem : v ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ) := (QuotientGroup.eq_one_iff v).mp hc
    rcases (Formalism.FrobeniusOrbits.Galois.mem_zpowers_neg_one v).mp hmem with h1 | h1
    · have h3 : ((1 + 2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 2))) = ((1 : ℕ) : ZMod (2 ^ (e + 2))) := by
        rw [← hv, h1, Units.val_one, Nat.cast_one]
      have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h3
      have hlt1 : 1 + 2 ^ (e + 1) < 2 ^ (e + 2) := by omega
      have hlt2 : 1 < 2 ^ (e + 2) := by omega
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at h4
      omega
    · have h3 : ((2 + 2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 2))) = ((0 : ℕ) : ZMod (2 ^ (e + 2))) := by
        have h5 : ((2 + 2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 2))) =
            ((1 + 2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 2))) + 1 := by
          push_cast
          ring
        rw [h5, ← hv, h1, Units.val_neg, Units.val_one, neg_add_cancel, Nat.cast_zero]
      have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h3
      have hlt3 : 2 + 2 ^ (e + 1) < 2 ^ (e + 2) := by omega
      rw [Nat.mod_eq_of_lt hlt3, Nat.zero_mod] at h4
      omega
  obtain ⟨u, hux, huy, huz, hg⟩ := exists_art (hH := hH) (g := ((1, 1), hcl e v))
    (x := 1 + 2 ^ (e + 1)) (y := 1) (z := 1) (v := v) (hv := hv) (hx := rfl)
    (hy := by simp) (hz := by simp) ..
  refine ⟨u, ?_, ?_⟩
  · have hN2 : 2 ^ (e + 2) * q * d / 2 = 2 ^ (e + 1) * q * d :=
      Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
    rw [hN2]
    have hux' : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 + 2 ^ (e + 1) [MOD 2 ^ (e + 1) * 2] := by
      rw [show 2 ^ (e + 1) * 2 = 2 ^ (e + 2) by ring]
      exact hux
    have hx1 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 1)] :=
      (Nat.ModEq.of_mul_right 2 hux').trans (by simp [Nat.ModEq])
    have hc1 : Nat.Coprime (2 ^ (e + 1)) q :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hqp).mpr (Ne.symm hq2))
    have hc2 : Nat.Coprime (2 ^ (e + 1) * q) d :=
      Nat.Coprime.mul (Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hdp).mpr (Ne.symm hd2)))
        ((Nat.coprime_primes hqp hdp).mpr hqd)
    exact (Nat.modEq_and_modEq_iff_modEq_mul hc2).mp
      ⟨(Nat.modEq_and_modEq_iff_modEq_mul hc1).mp ⟨hx1, huy⟩, huz⟩
  · intro h0
    rw [← hg] at h0
    exact hvne (congrArg Prod.snd h0)

theorem splitK_E (p : ℕ) (hp : p.Prime) :
    (primesOver (span {(p : ℤ)}) (𝓞 (KinE ζ a b))).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(d : ℤ)) p = 1)) :=
  SplitK.clause (L := hostE ζ a b) (b := bE ζ a b) hH.2.1 (by have := hH.2.2.2.1; omega)
    (by apply Subtype.ext; push_cast; exact h.2.2.1) p hp

theorem rd_eq : |(discr (hostE ζ a b) : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ (hostE ζ a b) : ℝ)) =
    (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d) := by
  rw [Formalism.FrobeniusOrbits.finrank_cmField hH.toHypOdd h]
  push_cast
  exact ((Formalism.FrobeniusOrbits.hostDiscr_of Formalism.FrobeniusOrbits.discriminant_real_subfield) e q d hH L ζ a b h).2.2.2.1

end Field

theorem real_ge (e q d : ℕ) (hq : 1 ≤ q) :
    (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt d ≤
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  nlinarith

theorem real_le (e : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * s ≤ ((2 ^ (e + 2) : ℕ) : ℝ) / 2 * s := by
  apply mul_le_mul_of_nonneg_right _ hs
  have h1 : ((2 ^ (e + 2) : ℕ) : ℝ) / 2 = (2 : ℝ) ^ ((e : ℝ) + 1) := by
    rw [show ((e : ℝ) + 1) = ((e + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    ring
  rw [h1]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (0 : ℝ) ≤ (2 : ℝ) ^ (-(e : ℝ)) := by positivity
  linarith

theorem real_sq (e q d : ℕ) (he : 2 ≤ e) (hq : 1 ≤ q) (hd : 1 ≤ d) :
    (4 * ((2 ^ e : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d)) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hqd : (1 : ℝ) ≤ (q : ℝ) * d := by nlinarith
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  have hx : (2 : ℝ) ^ (-(e : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    linarith
  have hpow : ((2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)))) ^ 2 =
      (2 : ℝ) ^ (2 * ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hpow]
  have h4 : (4 * ((2 ^ e : ℕ) : ℝ)) = (2 : ℝ) ^ ((e : ℝ) + 2) := by
    rw [show ((e : ℝ) + 2) = ((e + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    ring
  rw [h4]
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)))) := by positivity
  calc (2 : ℝ) ^ ((e : ℝ) + 2) ≤ (2 : ℝ) ^ (2 * ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)))) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
    _ ≤ _ := by nlinarith

variable (φ : Frame) (hinj : Function.Injective φ.h)
  {q d : ℕ} (hH : HostHyp q d) (he : 2 ≤ φ.e) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (φ.e + 2) q d ζ a b)

theorem gal_eq (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (hostRaw φ hinj hH he h).gal σ = ggIso φ hinj (galE φ.e ζ a b σ) := rfl

theorem gal_eq_art (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (u : (ZMod (2 ^ (φ.e + 2) * q * d))ˣ) :
    (hostRaw φ hinj hH he h).gal σ = (hostRaw φ hinj hH he h).art u ↔ galE φ.e ζ a b σ = art0 φ.e hH u := by
  rw [gal_eq]
  exact (ggIso φ hinj).injective.eq_iff

theorem gal_eq_cc (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (hostRaw φ hinj hH he h).gal σ = φ.cc ↔ galE φ.e ζ a b σ = cc φ.e := by
  rw [gal_eq]
  exact ggIso_eq_iff φ hinj _ c0

theorem galE_conj : galE φ.e ζ a b (hostRaw φ hinj hH he h).conj = cc φ.e := by
  have h2 : (hostRaw φ hinj hH he h).gal (hostRaw φ hinj hH he h).conj = φ.cc :=
    (hostRaw φ hinj hH he h).gal.apply_symm_apply φ.cc
  exact (gal_eq_cc φ hinj hH he h _).mp h2

theorem cc_mem_zpowers (g : FrobeniusOrbits.GG φ.e) : φ.cc ∈ Subgroup.zpowers (ggIso φ hinj g) ↔ g = cc φ.e := by
  have hcc : φ.cc = ggIso φ hinj (cc φ.e) := (ggIso_mk_one φ hinj c0).symm
  rw [hcc, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← map_zpow] at hk
    have hk' : g ^ k = cc φ.e := (ggIso φ hinj).injective hk
    have h1 : g.1 ^ k = c0 := congrArg Prod.fst hk'
    have h2 : g.2 ^ k = 1 := congrArg Prod.snd hk'
    have hsq : g.1 ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact Prod.ext (Int.units_mul_self _) (Int.units_mul_self _)
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, hsq, one_zpow] at h1
      exfalso
      have := congrArg (fun x : G0 => ((x.1 : ℤˣ) : ℤ)) h1
      norm_num [c0] at this
    · rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul] at h1
      have hd1 : orderOf g.2 ∣ 2 ^ φ.e := by
        have := orderOf_dvd_natCard g.2
        rwa [Formalism.FrobeniusOrbits.Group.card_H] at this
      obtain ⟨i, -, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
      have hk2 : ((orderOf g.2 : ℕ) : ℤ) ∣ 2 * m + 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
      have hi0 : i = 0 := by
        by_contra hne
        have h2d : (2 : ℤ) ∣ 2 * m + 1 := by
          refine dvd_trans ?_ hk2
          rw [hoi]
          push_cast
          exact dvd_pow_self 2 hne
        omega
      have ht : g.2 = 1 := by
        rw [← orderOf_eq_one_iff, hoi, hi0, pow_zero]
      exact Prod.ext h1 ht
  · rintro rfl
    exact ⟨1, zpow_one _⟩

def sqq : (hostRaw φ hinj hH he h).E := aE ζ a b

theorem sqq_sq : sqq φ hinj hH he h ^ 2 = -(q : (hostRaw φ hinj hH he h).E) := by
  apply Subtype.ext
  push_cast
  exact h.2.1

include hH h in
theorem gal_sqq (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    σ (aE ζ a b) = ((((galE φ.e ζ a b σ).1.1 : ℤˣ) : ℤ) : hostE ζ a b) * aE ζ a b := by
  apply Subtype.ext
  push_cast
  exact galE_aE hH.toHypOdd h σ

theorem psQ : (hostRaw φ hinj hH he h).PsQ := by
  intro u
  show (((ggIso φ hinj (art0 φ.e hH u)).1.1 : ℤˣ) : ℤ) = _
  rw [ggIso_fst]
  apply artinMap_first_eq_jacobiSym_of_modEq
  exact Nat.ModEq.refl _

theorem exact : (hostRaw φ hinj hH he h).Exact := by
  intro l hl hld
  have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hld)
  subst hl2
  obtain ⟨u, hu1, hu2⟩ := exact_art (e := φ.e) hH (by omega)
  refine ⟨u, hu1, fun hc => hu2 ?_⟩
  apply (ggIso φ hinj).injective
  rw [map_one]
  exact hc

theorem hostDer : HostDer (hostRaw φ hinj hH he h) := by
  have hqd := hH.toHypOdd
  have hord := ord_eq φ hinj
  have hc := galE_conj φ hinj hH he h
  have hdisc := hostDiscr_of discriminant_real_subfield φ.e q d hH L ζ a b h
  have hcase : ∀ {l : ℕ}, l.Prime → l ∣ 2 ^ (φ.e + 2) * q * d → (l = 2 ∨ l = q ∨ (l = d ∧ 2 ≤ φ.e)) := fun hl hN =>
    ((dvd_N_iff φ.e hH hl).mp hN).imp_right (Or.imp_right fun h1 => ⟨h1, he⟩)
  have hncase : ∀ {l : ℕ}, l.Prime → ¬ l ∣ 2 ^ (φ.e + 2) * q * d → (l ≠ 2 ∧ l ≠ q ∧ l ≠ d) := fun hl hN => by
    rwa [dvd_N_iff φ.e hH hl, not_or, not_or] at hN
  refine
    { art_surj := (ggIso φ hinj).surjective.comp (art0_surjective φ.e hH)
      cm := isCMField_hostE hqd h
      conj_iff := fun ψ σ => (isConj_iff_galE hqd h ψ σ).trans (gal_eq_cc φ hinj hH he h σ).symm
      finrank_E := (finrank_cmField hqd h).trans (by rw [hord]; ring)
      finrank_F := (finrank_hostF hqd h).trans (by rw [hord]; ring)
      mem_F := fun x => by
        rw [(eq_conjE_iff hqd h _).mpr hc]
        exact conjE_mem_hostF_iff hqd h x
      cmType := ⟨(Final.cmType φ.e q d hqd L ζ a b h).1,
        (Final.cmType φ.e q d hqd L ζ a b h).2.1.trans (by rw [hord]; ring), (Final.cmType φ.e q d hqd L ζ a b h).2.2⟩
      ps_root := ⟨aE ζ a b, ?_, gal_sqq φ hH h⟩
      art_ch := artinMap_second_eq_jacobiSym φ.e hH
      ps_d := fun u hu => Units.ext ((artinMap_first_eq_jacobiSym_of_modEq φ.e hH u (hu.of_dvd (dvd_mul_left _ _))).trans (jac_dq hH))
      frob := fun p _ hp (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(p : ℤ)})) =>
        ?_
      frob_any := fun l _ (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(l : ℤ)}))
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) => (frob_any_art hH h l P σ).trans
        (exists_congr fun u => and_congr_right fun _ => (gal_eq_art φ hinj hH he h σ u).symm)
      inertia := fun l _ (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(l : ℤ)}))
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) => (inertia_art hH h l P σ).trans
        (exists_congr fun u => and_congr_right fun _ => (gal_eq_art φ hinj hH he h σ u).symm)
      decomp := fun l _ (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(l : ℤ)}))
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) => (decomp_art hH h l P σ).trans
        (exists_congr fun u => exists_congr fun _ => and_congr_right fun _ => (gal_eq_art φ hinj hH he h σ u).symm)
      inertia_d := fun (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(d : ℤ)}))
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) => ((hostInertia φ.e q d hH L ζ a b h σ).2.2 P).trans
        (or_congr (ggIso_eq_iff φ hinj _ 1).symm (ggIso_eq_iff φ hinj _ (1, -1)).symm)
      decomp_typeI := fun l hl hN (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(l : ℤ)}))
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) hσ => ?_
      decompConj := fun l hl hN (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(l : ℤ)})) =>
        hostDecompConj φ.e q d hH L ζ a b h _ hc l (hcase hl hN) P
      unramEF := fun P hP hP0 => hostUnramEF φ.e q d hH L ζ a b h P hP hP0 _ hc
      splitK := splitK_E hH h
      ordinary := fun p _ (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(p : ℤ)})) =>
        (hostOrdinary φ.e q d hH L ζ a b h p P).trans
        (((Final.splitK φ.e q d hH L ζ a b h).1 p Fact.out).trans (splitK_E hH h p Fact.out).symm)
      eta := ⟨(hostEta φ.e q d hH L ζ a b h).1, fun p _ hp (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(p : ℤ)}))
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) hσ => ?_,
        fun p _ hp (P : Ideal (𝓞 (hostE ζ a b))) (_ : P.IsPrime) (_ : P.LiesOver (span {(p : ℤ)})) =>
        (hostEta φ.e q d hH L ζ a b h).2.2 p (hcase Fact.out hp) P⟩
      diffSupport := fun P hP hdvd => ?_
      principal := principal_stable hH h _ hc
      unimodular := hostUnimodular φ.e q d hH L ζ a b h _ hc
      discr_sq := hdisc.2.2.1
      discr_primes := ?_
      rd_ge := (real_ge φ.e q d hH.1.pos).trans (rd_eq hH h).ge
      rd_le := (rd_eq hH h).le.trans (real_le φ.e _ (Real.sqrt_nonneg _))
      rd_sq_ge := ?_
      norm_mu := norm_mu hH h }
  · intro h0
    have h1 : a = 0 := congrArg Subtype.val h0
    have h2 := h.2.1
    rw [h1] at h2
    have h3 : (q : L) = 0 := by simpa using h2.symm
    exact hH.1.ne_zero (by exact_mod_cast h3)
  · have hp' : p.Prime := Fact.out
    obtain ⟨n2, nq, nd⟩ := hncase hp' hp
    obtain ⟨f1, f2, f3⟩ := Final.frob φ.e q d hqd L ζ a b h p n2 nq nd P
    refine ⟨f1, fun σ u hu => (frob_art hH h p hp P σ u hu).trans (gal_eq_art φ hinj hH he h σ u).symm,
      fun σ hσ => ?_, f3⟩
    have hcop : Nat.Coprime p (2 ^ (φ.e + 2) * q * d) := (Nat.Prime.coprime_iff_not_dvd hp').mpr hp
    obtain ⟨-, g2, v, g3, g4⟩ := (f2 σ).mp hσ
    refine ⟨?_, g2, v, g3, (hH_ggIso φ hinj _).trans g4⟩
    have h1 := (gal_eq_art φ hinj hH he h σ _).mpr
      ((frob_art hH h p hp P σ (ZMod.unitOfCoprime p hcop) (ZMod.coe_unitOfCoprime _ _)).mp hσ)
    rw [h1, HostRaw.psAt, dif_pos (show Nat.Coprime p (hostRaw φ hinj hH he h).condN from hcop)]
    rfl
  · have hm : ((l : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by
      have : Fact l.Prime := ⟨hl⟩
      exact (odd_intCast_mem_iff l P _).mpr dvd_rfl
    have hr : l = 2 ∨ l = q := by
      rcases hl.dvd_mul.mp hN with h1 | h1
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h1))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hl hH.1).mp h1)
    exact Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.stab_Psi hH h l hr P hm σ hσ
  · obtain ⟨n2, nq, nd⟩ := hncase Fact.out hp
    exact ((hostEta φ.e q d hH L ζ a b h).2.1 p n2 nq nd P σ hσ).trans (cc_mem_zpowers φ hinj _).symm
  · show ((2 ^ (φ.e + 2) * q : ℕ) : 𝓞 (hostE ζ a b)) ∈ P
    push_cast
    rcases hostDiffSupport φ.e q d hH L ζ a b h P hP hdvd with h1 | h1
    · exact P.mul_mem_right _ (P.pow_mem_of_mem (by exact_mod_cast h1) _ (by omega))
    · exact P.mul_mem_left _ (by exact_mod_cast h1)
  · have h0 : discr (hostRaw φ hinj hH he h).E = _ := hdisc.1
    rw [h0]
    show (∀ p : ℕ, p.Prime → _ → p ∣ 2 ^ (φ.e + 2) * q * d) ∧ _ ∧ (d : ℤ) ∣ _
    refine ⟨fun p hp hd => ?_, ?_, ?_⟩
    · have hp' := Nat.prime_iff_prime_int.mp hp
      rcases hp'.dvd_or_dvd hd with h1 | h1
      · have h2 : p ∣ 2 := by exact_mod_cast hp'.dvd_of_dvd_pow h1
        exact h2.trans ((dvd_pow_self 2 (by omega)).trans (two_dvd φ.e q d))
      · have h2 : p ∣ q * d := by exact_mod_cast hp'.dvd_of_dvd_pow h1
        rw [mul_assoc]
        exact h2.mul_left _
    · refine (dvd_pow_self 2 ?_).mul_right _
      have h1 : 2 ^ 2 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ 2 * 3 ≤ 2 ^ (φ.e + 2) * (φ.e + 1) := Nat.mul_le_mul h1 (by omega)
      omega
    · refine (dvd_trans ?_ (dvd_pow_self _ (by positivity))).mul_left _
      push_cast
      exact dvd_mul_left _ _
  · have h1 : (hostRaw φ hinj hH he h).rd = _ := rd_eq hH h
    rw [h1, hord]
    exact real_sq φ.e q d he hH.1.pos hH.2.1.pos

def hostAx : HostAx φ := ⟨hostRaw φ hinj hH he h, hostDer φ hinj hH he h⟩

include hinj in
theorem twoGroup : φ.TwoGroup := ⟨φ.e, ord_eq φ hinj⟩

theorem muPM (hq : q ≠ 3) : (hostRaw φ hinj hH he h).MuPM := fun x hx => Formalism.FrobeniusOrbits.Final.host_field.2.2.2.2.2.2.2.2.2.2.1 φ.e q d hH hq L ζ a b h x hx

theorem coprimeFifteen_of_coprime : (hostRaw φ hinj hH he h).CoprimeFifteen := by
  show Nat.Coprime (2 ^ (φ.e + 2)) 15
  exact Nat.Coprime.pow_left _ (by norm_num)

include hinj he in
theorem qs_le : 2 ^ (φ.e + 2) ≤ φ.ord ^ 2 := by
  rw [ord_eq φ hinj, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end D7

theorem exists_hostAx (φ : Frame) (hinj : Function.Injective φ.h) (he : 2 ≤ φ.e) {q d : ℕ} (hH : FrobeniusOrbits.HostHyp q d) :
    ∃ H : HostAx φ, H.q = q ∧ H.d = d ∧ H.QS = 2 ^ (φ.e + 2) ∧ φ.TwoGroup ∧ H.toHostRaw.CoprimeFifteen ∧
      (q ≠ 3 → H.toHostRaw.MuPM) ∧ H.toHostRaw.PsQ ∧ H.toHostRaw.Exact ∧
      ∃ s : H.E, s ^ 2 = -(H.q : H.E) ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ s = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * s := by
  obtain ⟨L, hF, hN, ζ, a, b, h⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists (φ.e + 2) q d
  exact ⟨D7.hostAx φ hinj hH he h, rfl, rfl, rfl, D7.twoGroup φ hinj, D7.coprimeFifteen_of_coprime φ hinj hH he h,
    fun hq => D7.muPM φ hinj hH he h hq, D7.psQ φ hinj hH he h, D7.exact φ hinj hH he h,
    D7.sqq φ hinj hH he h, D7.sqq_sq φ hinj hH he h, fun σ => D7.gal_sqq φ hH h σ⟩

end Formalism.HC

end
