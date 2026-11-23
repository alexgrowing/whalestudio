import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RootEqOfSubMem
import Mathlib

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem sq_two_pow {d : ℤ} (hd : d % 8 = 7) (k : ℕ) : ∃ s : ℤ, (2 : ℤ) ^ (k + 3) ∣ s ^ 2 + d := by
  induction k with
  | zero => exact ⟨1, by norm_num; omega⟩
  | succ k ih =>
    obtain ⟨s, t, ht⟩ := ih
    have e3 : (2 : ℤ) ^ (k + 3) = 8 * 2 ^ k := by ring
    rw [e3] at ht
    have hs1 : s % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one s with hs0 | hs1
      · exfalso
        obtain ⟨c, rfl⟩ : ∃ c, s = 2 * c := ⟨s / 2, by omega⟩
        have hd2 : d = 2 * (4 * 2 ^ k * t - 2 * c ^ 2) := by linear_combination ht
        have : d % 2 = 0 := by rw [hd2]; exact Int.mul_emod_right 2 _
        omega
      · exact hs1
    obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := ⟨s / 2, by omega⟩
    rcases Int.emod_two_eq_zero_or_one t with ht0 | ht1
    · obtain ⟨b, rfl⟩ : ∃ b, t = 2 * b := ⟨t / 2, by omega⟩
      refine ⟨2 * a + 1, b, ?_⟩
      have e4 : (2 : ℤ) ^ (k + 1 + 3) = 16 * 2 ^ k := by ring
      rw [e4]
      linear_combination ht
    · obtain ⟨b, rfl⟩ : ∃ b, t = 2 * b + 1 := ⟨t / 2, by omega⟩
      refine ⟨2 * a + 1 + 2 ^ (k + 2), a + b + 1 + 2 ^ k, ?_⟩
      have e2 : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by ring
      have e4 : (2 : ℤ) ^ (k + 1 + 3) = 16 * 2 ^ k := by ring
      rw [e2, e4]
      linear_combination ht

theorem sq_odd_pow {d : ℤ} {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hj : jacobiSym (-d) l = 1) (k : ℕ) :
    ∃ s : ℤ, (l : ℤ) ^ (k + 1) ∣ s ^ 2 + d := by
  haveI := Fact.mk hl
  have hl2' : (2 : ZMod l) ≠ 0 := by
    intro h
    have h' : ((2 : ℤ) : ZMod l) = 0 := by exact_mod_cast h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    have h'' : l ∣ 2 := by exact_mod_cast h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h'')
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have hd0 : ((-d : ℤ) : ZMod l) ≠ 0 := by
    intro h
    rw [(legendreSym.eq_zero_iff l (-d)).mpr h] at hj
    norm_num at hj
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff l hd0).mp hj
  induction k with
  | zero =>
    refine ⟨(r.val : ℤ), ?_⟩
    rw [zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    push_cast at hr
    linear_combination (-1 : ZMod l) * hr
  | succ k ih =>
    obtain ⟨s, t, ht⟩ := ih
    have hs0 : (s : ZMod l) ≠ 0 := by
      intro h
      have h1 : ((s ^ 2 + d : ℤ) : ZMod l) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
        exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero k)) t
      push_cast at h1
      rw [h] at h1
      apply hd0
      push_cast
      linear_combination -h1
    have h2s : (2 * (s : ZMod l)) ≠ 0 := mul_ne_zero hl2' hs0
    obtain ⟨c, hc'⟩ := ZMod.intCast_surjective (n := l) (-(t : ZMod l) * (2 * (s : ZMod l))⁻¹)
    have hc : ((t + 2 * s * c : ℤ) : ZMod l) = 0 := by
      push_cast
      rw [hc']
      have hi : (2 * (s : ZMod l)) * (2 * (s : ZMod l))⁻¹ = 1 := mul_inv_cancel₀ h2s
      linear_combination (-(t : ZMod l)) * hi
    obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp hc
    refine ⟨s + (l : ℤ) ^ (k + 1) * c, w + (l : ℤ) ^ k * c ^ 2, ?_⟩
    linear_combination ht + (l : ℤ) ^ (k + 1) * hw

theorem sq_mod {d : ℤ} (hd : d % 8 = 7) (m : ℕ) (hm0 : m ≠ 0)
    (hm : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ m → jacobiSym (-d) l = 1) : ∃ s : ℤ, (m : ℤ) ∣ s ^ 2 + d := by
  revert hm0 hm
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p n hp =>
    intro _ hm
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨s, hs⟩ := sq_two_pow hd n
      exact ⟨s, by push_cast; exact (pow_dvd_pow 2 (by omega)).trans hs⟩
    · rcases n with _ | n
      · exact ⟨0, by simp⟩
      · obtain ⟨s, hs⟩ := sq_odd_pow hp hp2 (hm p hp hp2 (dvd_pow_self p (Nat.succ_ne_zero n))) n
        exact ⟨s, by push_cast; exact hs⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ hm
    obtain ⟨sa, hsa⟩ := iha (by omega) (fun l hl hl2 hla => hm l hl hl2 (Dvd.dvd.mul_right hla b))
    obtain ⟨sb, hsb⟩ := ihb (by omega) (fun l hl hl2 hlb => hm l hl hl2 (Dvd.dvd.mul_left hlb a))
    have hco : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
    obtain ⟨x, y, hxy⟩ := hco
    refine ⟨sa + a * (x * (sb - sa)), ?_⟩
    push_cast
    apply IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr hab)
    · obtain ⟨k, hk⟩ := hsa
      exact ⟨k + 2 * sa * (x * (sb - sa)) + a * (x * (sb - sa)) ^ 2, by linear_combination hk⟩
    · obtain ⟨k, hk⟩ := hsb
      refine ⟨k + 2 * sb * (-y * (sb - sa)) + b * (-y * (sb - sa)) ^ 2, ?_⟩
      linear_combination hk + (sb - sa) * ((sa + a * (x * (sb - sa))) +
        (sb + b * (-y * (sb - sa)))) * hxy

theorem exists_unit_crt {A B : ℕ} [NeZero (A * B)] (hAB : A.Coprime B) (x y : ℕ) (hx : x.Coprime A) (hy : y.Coprime B) :
    ∃ u : (ZMod (A * B))ˣ, (u : ZMod (A * B)).val ≡ x [MOD A] ∧ (u : ZMod (A * B)).val ≡ y [MOD B] := by
  let z := Nat.chineseRemainder hAB x y
  have hzA : (z : ℕ) ≡ x [MOD A] := z.2.1
  have hzB : (z : ℕ) ≡ y [MOD B] := z.2.2
  have hcA : Nat.Coprime z A := by rw [Nat.Coprime, Nat.ModEq.gcd_eq hzA]; exact hx
  have hcB : Nat.Coprime z B := by rw [Nat.Coprime, Nat.ModEq.gcd_eq hzB]; exact hy
  refine ⟨ZMod.unitOfCoprime z (Nat.Coprime.mul_right hcA hcB), ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq z (A * B)).of_mul_right B).trans hzA
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq z (A * B)).of_mul_left A).trans hzB

theorem exists_prime_liesOver {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.LiesOver (span {(p : ℤ)}) := by
  have hne : Ideal.comap (algebraMap ℤ (𝓞 M)) P ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.comap (algebraMap ℤ (𝓞 M)) P = Ideal.span {g} :=
    (Submodule.IsPrincipal.principal (Ideal.comap (algebraMap ℤ (𝓞 M)) P))
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [hg, Ideal.span_singleton_eq_bot]
  have hpr : (Ideal.span {g}).IsPrime := by rw [← hg]; infer_instance
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp hpr
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ⟨?_⟩⟩
  rw [Int.span_natAbs]
  exact hg.symm

variable {φ : Frame} (H : HostRaw φ)

theorem two_dvd_QS : 2 ∣ H.QS := (dvd_pow_self 2 (by omega : φ.e + 2 ≠ 0)).trans H.tower_dvd

theorem tower_dvd_QSq : 2 ^ (φ.e + 2) ∣ H.QS * H.q := H.tower_dvd.trans (dvd_mul_right _ _)

theorem QSq_dvd : H.QS * H.q ∣ H.condN := dvd_mul_right _ _

theorem cop_QSq_d : Nat.Coprime (H.QS * H.q) H.d := by
  have hqd : H.q ≠ H.d := by
    intro h
    have h1 := H.hyp.2.2.1
    have h2 := H.hyp.2.2.2.1
    rw [h] at h1
    omega
  have hq : Nat.Coprime H.q H.d := (Nat.coprime_primes H.hyp.1 H.hyp.2.1).mpr hqd
  exact Nat.Coprime.mul (Nat.Coprime.coprime_mul_left_right H.QS_coprime) hq

theorem split_QSq (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (h : l ∣ H.QS * H.q) : jacobiSym (-(H.d : ℤ)) l = 1 := by
  rcases (Nat.Prime.dvd_mul hl).mp h with h1 | h1
  · exact H.QS_split l hl hl2 h1
  · have hlq : l = H.q := (Nat.prime_dvd_prime_iff_eq hl H.hyp.1).mp h1
    rw [hlq]
    exact H.hyp.2.2.2.2

theorem ordCompl_d : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hd : H.d.Prime := H.hyp.2.1
  have hnd : ¬ H.d ∣ H.QS * H.q := fun h => hd.one_lt.ne' ((cop_QSq_d H).symm.eq_one_of_dvd h)
  show ordCompl[H.d] (H.QS * H.q * H.d) = H.QS * H.q
  rw [show H.QS * H.q * H.d = H.d ^ 1 * (H.QS * H.q) by ring]
  exact Formalism.HC.D7.ordCompl_eq hd 1 hnd

theorem ps_congr (u w : (ZMod H.condN)ˣ) (h : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) w) :
    (H.art u).1.1 = (H.art w).1.1 := by
  haveI : NeZero H.condN := ⟨Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos)⟩
  have h1 : ZMod.unitsMap (QSq_dvd H) (u * w⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := H.art_d (u * w⁻¹) ((val_modEq_one_iff (QSq_dvd H) _).mpr h1)
  have h3 : (H.art (u * w⁻¹)).1.1 = 1 := by
    rcases h2 with h2 | h2 <;> rw [h2] <;> rfl
  have h4 : H.art u = H.art (u * w⁻¹) * H.art w := by rw [← map_mul, inv_mul_cancel_right]
  rw [h4, Prod.fst_mul, Prod.fst_mul, h3, one_mul]

theorem ps_d : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] → (H.art u).1.1 = -1 := by
  intro u hu
  have hM0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  haveI : NeZero (H.QS * H.q) := ⟨hM0⟩
  have hd8 : (H.d : ℤ) % 8 = 7 := by have := H.hyp.2.2.2.1; omega
  obtain ⟨s, hs⟩ := sq_mod hd8 (H.QS * H.q) hM0 (split_QSq H)
  have hs' : ((s : ZMod (H.QS * H.q))) ^ 2 = -((H.d : ℕ) : ZMod (H.QS * H.q)) := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hs
    push_cast at h0
    linear_combination h0
  have hdu : IsUnit ((H.d : ℕ) : ZMod (H.QS * H.q)) :=
    (ZMod.unitOfCoprime H.d (cop_QSq_d H).symm).isUnit
  have hsu : IsUnit ((s : ZMod (H.QS * H.q))) := by
    have h0 : IsUnit ((s : ZMod (H.QS * H.q)) ^ 2) := by rw [hs']; exact hdu.neg
    exact (isUnit_pow_iff two_ne_zero).mp h0
  obtain ⟨w, hw⟩ := ZMod.unitsMap_surjective (QSq_dvd H) hsu.unit
  have hneg : ((ZMod.unitsMap (QSq_dvd H) (-1) : (ZMod (H.QS * H.q))ˣ) : ZMod (H.QS * H.q)) = -1 := by
    simp [ZMod.unitsMap]
  have key : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) (-1 * w ^ 2) := by
    apply Units.ext
    rw [(val_modEq_iff (QSq_dvd H) u H.d).mp hu, map_mul, map_pow, hw, Units.val_mul,
      Units.val_pow_eq_pow_val, IsUnit.unit_spec, hs', hneg]
    ring
  have h1 := ps_congr H u (-1 * w ^ 2) key
  rw [h1, map_mul, map_pow, H.art_neg_one, Prod.fst_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_fst,
    Int.units_sq, mul_one]
  rfl

theorem cc_ne_one : φ.cc ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : φ.GG => ((g.1.2 : ℤˣ) : ℤ)) h
  simp [Frame.cc, c0] at h1

theorem cc_not_mem_Psi : φ.cc ∉ φ.Psi := by
  intro h
  have h1 : φ.chD φ.cc = 1 := MonoidHom.mem_ker.mp h
  have h2 : φ.chD φ.cc = -1 := rfl
  rw [h2] at h1
  exact absurd (congrArg Units.val h1) (by norm_num)

theorem val_one_modEq (M N : ℕ) [NeZero N] (h : M ∣ N) : (((1 : (ZMod N)ˣ) : ZMod N)).val ≡ 1 [MOD M] := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod]
  exact (Nat.mod_modEq 1 N).of_dvd h

private theorem jac_lemma {p d : ℕ} (hp : p % 2 = 1) (hd : d % 4 = 3) :
    jacobiSym (-(d : ℤ)) p = jacobiSym (p : ℤ) d := by
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hp)]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h (Nat.odd_iff.mpr (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd h]
    ring

private theorem art_snd_lemma (u : (ZMod H.condN)ˣ) :
    (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hz := Cond.z_spec H.condN
  have hx : IsPrimitiveRoot (Cond.z H.condN ^ (H.QS * H.q)) H.d :=
    hz.pow (Nat.pos_of_ne_zero (NeZero.ne H.condN)) rfl
  have hg2 : Cond.gs H.d hx.pow_eq_one ^ 2 = -(H.d : Cond.Cyc H.condN) := Cond.gs_sq hd4 hx
  have hy2 : (emb H H.sqd) ^ 2 = -(H.d : Cond.Cyc H.condN) := by
    rw [← map_pow, H.sqd_sq, map_neg, map_natCast]
  have hy0 : emb H H.sqd ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hy2
    have h0 : (H.d : Cond.Cyc H.condN) = 0 := by linear_combination hy2
    exact H.hyp.2.1.ne_zero (by exact_mod_cast h0)
  have hτx : (tauN H.condN u) (Cond.z H.condN ^ (H.QS * H.q)) =
      (Cond.z H.condN ^ (H.QS * H.q)) ^ (u : ZMod H.condN).val :=
    tauN_root H.condN u _ (by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow])
  have hcopv : Nat.Coprime (u : ZMod H.condN).val H.d :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left H.d (H.QS * H.q)) (ZMod.val_coe_unit_coprime u)
  have hτg : (tauN H.condN u) (Cond.gs H.d hx.pow_eq_one) =
      ((jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d : ℤ) : Cond.Cyc H.condN) *
        Cond.gs H.d hx.pow_eq_one :=
    Formalism.HC.D7.gs_act hx.pow_eq_one
      ((tauN H.condN u : Cond.Cyc H.condN ≃ₐ[ℚ] Cond.Cyc H.condN) : Cond.Cyc H.condN →+* Cond.Cyc H.condN)
      _ hτx hcopv
  have hτy : (tauN H.condN u) (emb H H.sqd) =
      ((jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d : ℤ) : Cond.Cyc H.condN) * emb H H.sqd := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy2.trans hg2.symm) with h | h
    · rw [h]
      exact hτg
    · rw [h, map_neg, hτg, mul_neg]
  have hσ := H.gal_sqd (H.gal.symm (H.art u))
  rw [MulEquiv.apply_symm_apply] at hσ
  have h2 := emb_art H u H.sqd
  rw [hσ, map_mul, map_intCast, hτy] at h2
  have h3 := mul_right_cancel₀ hy0 h2
  exact_mod_cast h3

theorem frob : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
  intro p _ hpN P _ _
  have hp : p.Prime := Fact.out
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hcop : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hfact : ordCompl[p] H.condN = H.condN := by
    rw [Nat.factorization_eq_zero_of_not_dvd hpN, pow_zero, Nat.div_one]
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, hI, hF⟩ := exists_over (emb H) p P
  have hval : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN) = p →
      (u : ZMod H.condN).val ≡ p [MOD ordCompl[p] H.condN] := by
    intro u hu
    rw [hfact, hu, ZMod.val_natCast]
    exact Nat.mod_modEq p _
  have hfu : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN) = p → ∀ σ : H.E ≃ₐ[ℚ] H.E,
      H.gal σ = H.art u → IsArithFrobAt ℤ σ P := fun u hu σ hσ =>
    hF σ (tauN H.condN u) ((gal_eq_art_iff H σ u).mp hσ) (tauN_frob H.condN p Q u (hval u hu))
  have hinert : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
    intro σ
    constructor
    · intro h
      obtain ⟨τ, hτ1, hτ2⟩ := (hI σ).mp h
      obtain ⟨w, rfl⟩ := (tauN H.condN).surjective τ
      have h1 := (tauN_inertia_iff H.condN p Q w).mp hτ2
      rw [hfact] at h1
      have hw1 : w = 1 := by
        apply Units.ext
        rw [Units.val_one, ← ZMod.natCast_zmod_val (w : ZMod H.condN), ← Nat.cast_one,
          ZMod.natCast_eq_natCast_iff]
        exact h1
      subst hw1
      apply AlgEquiv.ext
      intro x
      apply (emb H).toRingHom.injective
      show emb H (σ x) = emb H x
      rw [hτ1 x, map_one, AlgEquiv.one_apply]
    · rintro rfl x
      simp
  have hiff : ∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
      (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u) := by
    intro σ u hu
    constructor
    · intro hσ
      have hσ' := hfu u hu (H.gal.symm (H.art u)) (H.gal.apply_symm_apply _)
      have h1 := (hinert _).mp ((frob_iff_inertia P _ σ hσ').mp hσ)
      rw [mul_inv_eq_one] at h1
      rw [h1, MulEquiv.apply_symm_apply]
    · exact hfu u hu σ
  have hu0 : ((ZMod.unitOfCoprime p hcop : (ZMod H.condN)ˣ) : ZMod H.condN) = p :=
    ZMod.coe_unitOfCoprime _ _
  refine ⟨⟨H.gal.symm (H.art (ZMod.unitOfCoprime p hcop)),
    hfu _ hu0 _ (H.gal.apply_symm_apply _)⟩, hiff, fun σ hσ => ?_, hinert⟩
  have hg := (hiff σ _ hu0).mp hσ
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN ((two_dvd_QS H).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    unfold HostRaw.psAt
    rw [dif_pos hcop]
  · rw [hg, art_snd_lemma H, hu0, ZMod.val_natCast, jac_lemma hpodd hd4,
      jacobiSym.mod_left ((p % H.condN : ℕ) : ℤ), jacobiSym.mod_left (p : ℤ)]
    congr 1
    push_cast
    exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)
  · have h2 : 2 ^ (φ.e + 2) ∣ H.condN := (tower_dvd_QSq H).trans (QSq_dvd H)
    have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    refine ⟨ZMod.unitOfCoprime p hc2, ZMod.coe_unitOfCoprime _ _, ?_⟩
    rw [hg]
    apply H.art_h
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq p H.condN).of_dvd h2).symm

theorem exists_art_iod : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hd1 : 1 ≤ H.d := H.hyp.2.1.one_lt.le
  have hcop : Nat.Coprime (H.d - 1) H.d :=
    ((Nat.Prime.coprime_iff_not_dvd H.hyp.2.1).mpr
      (Nat.not_dvd_of_pos_of_lt (by have := H.hyp.2.1.two_le; omega) (by omega))).symm
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (cop_QSq_d H) 1 (H.d - 1) (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hdv : H.d ∣ (u : ZMod H.condN).val + 1 := by
    have h0 : ((u : ZMod H.condN).val + 1) % H.d = (H.d - 1 + 1) % H.d := hu2.add_right 1
    rw [Nat.sub_add_cancel hd1, Nat.mod_self] at h0
    exact Nat.dvd_of_mod_eq_zero h0
  have hv : ((u : ZMod H.condN).val : ℤ) % (H.d : ℤ) = (-1 : ℤ) % (H.d : ℤ) := by
    have h0 : (H.d : ℤ) ∣ ((u : ZMod H.condN).val : ℤ) + 1 := by exact_mod_cast hdv
    have h1 : Int.ModEq (H.d : ℤ) ((u : ZMod H.condN).val : ℤ) (-1) := by
      apply Int.modEq_iff_dvd.mpr
      rw [show (-1 : ℤ) - ((u : ZMod H.condN).val : ℤ) = -(((u : ZMod H.condN).val : ℤ) + 1) by ring]
      exact h0.neg_right
    exact h1
  have hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = -1 := by
    rw [jacobiSym.mod_left, hv, ← jacobiSym.mod_left,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hd4]
  rcases H.art_d u hu1 with h | h
  · exfalso
    have h0 := art_snd_lemma H u
    rw [h, hJ] at h0
    norm_num at h0
  · exact h

theorem inertia_d : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod) := by
  intro P _ _ σ
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, hI, -⟩ := exists_over (emb H) H.d P
  constructor
  · intro h
    obtain ⟨τ, hτ1, hτ2⟩ := (hI σ).mp h
    obtain ⟨w, rfl⟩ := (tauN H.condN).surjective τ
    have h1 := (tauN_inertia_iff H.condN H.d Q w).mp hτ2
    rw [ordCompl_d H] at h1
    have hg : H.gal σ = H.art w := (gal_eq_art_iff H σ w).mpr hτ1
    rw [hg]
    exact H.art_d w h1
  · intro h
    have key : ∀ w : (ZMod H.condN)ˣ, (w : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] →
        H.gal σ = H.art w → ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
      intro w hw1 hg
      apply (hI σ).mpr
      refine ⟨tauN H.condN w, (gal_eq_art_iff H σ w).mp hg, ?_⟩
      apply (tauN_inertia_iff H.condN H.d Q w).mpr
      rw [ordCompl_d H]
      exact hw1
    rcases h with h | h
    · exact key 1 (val_one_modEq _ _ (QSq_dvd H)) (h.trans (map_one _).symm)
    · obtain ⟨u, hu1, hu2⟩ := exists_art_iod H
      exact key u hu1 (h.trans hu2.symm)

theorem decomp_typeI : ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ φ.Psi := by
  intro l hl hlN P _ _ σ hσ
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  show (H.gal σ).1.2 = 1
  rcases Int.units_eq_one_or ((H.gal σ).1.2) with hε | hε
  · exact hε
  exfalso
  have hσX : σ H.sqd = -H.sqd := by rw [H.gal_sqd σ, hε]; simp
  have hM0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  have hd8 : (H.d : ℤ) % 8 = 7 := by have := H.hyp.2.2.2.1; omega
  obtain ⟨s, hs⟩ := sq_mod hd8 (H.QS * H.q) hM0 (split_QSq H)
  have h16 : 2 ^ 4 ∣ H.QS * H.q :=
    ((pow_dvd_pow 2 (by have := H.two_le_e; omega)).trans H.tower_dvd).trans (dvd_mul_right _ _)
  obtain ⟨R, hR⟩ := h16
  obtain ⟨c, hc⟩ := hs
  have hc' : s ^ 2 + (H.d : ℤ) = 16 * ((R : ℤ) * c) := by rw [hc, hR]; push_cast; ring
  obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := by
    rcases Int.even_or_odd s with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exfalso
      have h0 : (H.d : ℤ) = 2 * (8 * ((R : ℤ) * c) - 2 * a ^ 2) := by linear_combination hc'
      generalize 8 * ((R : ℤ) * c) - 2 * a ^ 2 = z at h0
      have := H.hyp.2.2.2.1
      omega
    · exact ⟨a, rfl⟩
  have hlP : ((l : ℤ) : 𝓞 H.E) ∈ P := by
    have h0 : (l : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.over_def P (span {(l : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under] using h0
  have hlR : l ∣ 4 * R := by
    rcases hl.eq_two_or_odd with rfl | hlo
    · exact Dvd.intro (2 * R) (by ring)
    · have h0 : l ∣ 2 ^ 4 * R := hR ▸ hlN
      have hco : Nat.Coprime l (2 ^ 4) :=
        Nat.Coprime.pow_right 4 ((Nat.coprime_primes hl Nat.prime_two).mpr (by omega))
      exact (hco.dvd_of_dvd_mul_left h0).mul_left 4
  obtain ⟨k, hk⟩ := hlR
  obtain ⟨ω, hωc⟩ : ∃ ω : 𝓞 H.E, (ω : H.E) = (1 + H.sqd) / 2 :=
    ⟨⟨(1 + H.sqd) / 2, Formalism.FrobeniusOrbits.Decomp.omega_integral hd4 H.sqd_sq⟩, rfl⟩
  have hσω : σ • ω = 1 - ω := by
    apply NumberField.RingOfIntegers.ext
    show σ (ω : H.E) = 1 - (ω : H.E)
    rw [hωc, map_div₀, map_add, map_one, hσX, show σ (2 : H.E) = 2 from map_ofNat σ 2]
    ring
  have hprod : (ω - ((a + 1 : ℤ) : 𝓞 H.E)) * (ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) =
      -((l : ℤ) : 𝓞 H.E) * ((k * c : ℤ) : 𝓞 H.E) := by
    apply NumberField.RingOfIntegers.ext
    show ((ω : H.E) - ((a + 1 : ℤ) : H.E)) * ((ω : H.E) - (1 - ((a + 1 : ℤ) : H.E))) =
      -((l : ℤ) : H.E) * ((k * c : ℤ) : H.E)
    rw [hωc]
    push_cast
    have hcE : (((2 * a + 1) ^ 2 + (H.d : ℤ) : ℤ) : H.E) = ((16 * ((R : ℤ) * c) : ℤ) : H.E) := by
      rw [hc']
    push_cast at hcE
    have hkE : (4 * (R : H.E)) = (l : H.E) * (k : H.E) := by exact_mod_cast hk
    linear_combination (1 / 4 : H.E) * H.sqd_sq - (1 / 4 : H.E) * hcE - (c : H.E) * hkE
  have hprodP : (ω - ((a + 1 : ℤ) : 𝓞 H.E)) * (ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) ∈ P := by
    rw [hprod]
    exact Ideal.mul_mem_right _ _ (neg_mem hlP)
  have hσt : σ • ((a + 1 : ℤ) : 𝓞 H.E) = ((a + 1 : ℤ) : 𝓞 H.E) :=
    map_intCast (MulSemiringAction.toRingHom (H.E ≃ₐ[ℚ] H.E) (𝓞 H.E) σ) (a + 1)
  have hA : ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P → ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P := by
    intro h
    have h1 := (Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab σ P hσ _).mpr h
    rw [smul_sub, hσω, hσt] at h1
    have h2 : ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) = -(1 - ω - ((a + 1 : ℤ) : 𝓞 H.E)) := by ring
    rw [h2]
    exact neg_mem h1
  have hB : ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P → ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P := by
    intro h
    have h1 := (Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab σ P hσ _).mpr h
    rw [smul_sub, smul_sub, hσω, hσt, smul_one] at h1
    have h2 : ω - ((a + 1 : ℤ) : 𝓞 H.E) = -(1 - ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) := by ring
    rw [h2]
    exact neg_mem h1
  have hboth : ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P ∧ ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P := by
    rcases (inferInstance : P.IsPrime).mem_or_mem hprodP with h | h
    · exact ⟨h, hA h⟩
    · exact ⟨hB h, h⟩
  have hsP : ((2 * a + 1 : ℤ) : 𝓞 H.E) ∈ P := by
    have h0 := P.sub_mem hboth.2 hboth.1
    have h1 : ((2 * a + 1 : ℤ) : 𝓞 H.E) =
        ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) - (ω - ((a + 1 : ℤ) : 𝓞 H.E)) := by
      push_cast
      ring
    rw [h1]
    exact h0
  have hls : (l : ℤ) ∣ 2 * a + 1 := by
    have h0 : (2 * a + 1 : ℤ) ∈ P.under ℤ := by simpa [Ideal.under] using hsP
    rw [← Ideal.over_def P (span {(l : ℤ)}), Ideal.mem_span_singleton] at h0
    exact h0
  have hlsd : (l : ℤ) ∣ (2 * a + 1) ^ 2 + H.d := by
    rw [hc]
    exact Dvd.dvd.mul_right (by exact_mod_cast hlN) c
  have hld : (l : ℤ) ∣ H.d := (dvd_add_right (dvd_pow hls two_ne_zero)).mp hlsd
  have hld' : l ∣ H.d := by exact_mod_cast hld
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hlN (cop_QSq_d H)) hld')

theorem decompConj : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P := by
  intro l hl hlN P _ _ hσ
  have h2 : H.gal H.conj = φ.cc := MulEquiv.apply_symm_apply _ _
  by_cases hlq : l ∣ H.QS * H.q
  · have h3 := decomp_typeI H l hl hlq P H.conj hσ
    rw [h2] at h3
    exact cc_not_mem_Psi h3
  have hld : l = H.d := by
    rcases (Nat.Prime.dvd_mul hl).mp hlN with h | h
    · exact absurd h hlq
    · exact (Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI hPd : P.LiesOver (span {(H.d : ℤ)}) := by rw [← hld]; infer_instance
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, -, hF⟩ := exists_over (emb H) H.d P
  have hcd : Nat.Coprime H.d (H.QS * H.q) := (cop_QSq_d H).symm
  obtain ⟨uF, huF1, -⟩ := exists_unit_crt (cop_QSq_d H) H.d 1 hcd (Nat.coprime_one_left _)
  have hFrob : IsArithFrobAt ℤ (H.gal.symm (H.art uF)) P := by
    apply hF _ (tauN H.condN uF) ((gal_eq_art_iff H _ uF).mp (H.gal.apply_symm_apply _))
    apply tauN_frob H.condN H.d Q uF
    rw [ordCompl_d H]
    exact huF1
  obtain ⟨k, ρ, hρ, hconj⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul H.d P _ H.conj hFrob hσ
  have hg : φ.cc = H.gal ρ * H.art uF ^ k := by
    rw [← h2, hconj, map_mul, map_pow, MulEquiv.apply_symm_apply]
  have hρ1 : (H.gal ρ).1.1 = 1 ∧ (H.gal ρ).2 = 1 := by
    rcases (inertia_d H P ρ).mp hρ with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
  have hps := ps_d H uF huF1
  have h2N : 2 ^ (φ.e + 2) ∣ H.QS * H.q := tower_dvd_QSq H
  have hc2 : Nat.Coprime H.d (2 ^ (φ.e + 2)) := Nat.Coprime.coprime_dvd_right h2N hcd
  have hhv : φ.hH (H.art uF).2 = hcl φ.e (ZMod.unitOfCoprime H.d hc2) := by
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff]
    exact (huF1.of_dvd h2N).symm
  have hk2 : (H.art uF).2 ^ k = 1 := by
    have h0 := congrArg Prod.snd hg
    rw [Prod.snd_mul, Prod.pow_snd, hρ1.2, one_mul] at h0
    rw [← h0]
    rfl
  have hvk : ((ZMod.unitOfCoprime H.d hc2 ^ k : (ZMod (2 ^ (φ.e + 2)))ˣ) : HGrp φ.e) = 1 := by
    rw [QuotientGroup.mk_pow]
    show hcl φ.e (ZMod.unitOfCoprime H.d hc2) ^ k = 1
    rw [← hhv, ← map_pow, hk2, map_one]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_one_iff _ |>.mp hvk)
  have h16 : 16 ∣ 2 ^ (φ.e + 2) := by
    have h0 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h0]
    exact pow_dvd_pow 2 (by have := H.two_le_e; omega)
  have hfv : ZMod.castHom h16 (ZMod 16) ((ZMod.unitOfCoprime H.d hc2 : (ZMod (2 ^ (φ.e + 2)))ˣ) :
      ZMod (2 ^ (φ.e + 2))) = 7 := by
    rw [ZMod.coe_unitOfCoprime, map_natCast, ← ZMod.natCast_mod H.d 16, H.hyp.2.2.2.1]
    rfl
  have hpm : (7 : ZMod 16) ^ k = 1 ∨ (7 : ZMod 16) ^ k = -1 := by
    have h0 := congrArg (fun x : (ZMod (2 ^ (φ.e + 2)))ˣ =>
      ZMod.castHom h16 (ZMod 16) (x : ZMod (2 ^ (φ.e + 2)))) hn
    simp only [Units.val_pow_eq_pow_val, map_pow, hfv] at h0
    rcases Int.even_or_odd n with he | ho
    · left
      rw [he.neg_one_zpow, Units.val_one, map_one] at h0
      exact h0.symm
    · right
      rw [ho.neg_one_zpow, Units.val_neg, Units.val_one, map_neg, map_one] at h0
      exact h0.symm
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h0 := congrArg (fun g : φ.GG => g.1.1) hg
    simp only [Prod.fst_mul, Prod.pow_fst] at h0
    rw [hρ1.1, hps, one_mul, hj, ← two_mul, pow_mul, Int.units_sq, one_pow] at h0
    have h1 : (-1 : ℤˣ) = 1 := h0
    exact absurd (congrArg Units.val h1) (by norm_num)
  · have h7 : (7 : ZMod 16) ^ k = 7 := by
      rw [hj, pow_succ, pow_mul, (by decide : (7 : ZMod 16) ^ 2 = 1), one_pow, one_mul]
    rw [h7] at hpm
    revert hpm
    decide

theorem unramEF : ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P := by
  intro P hP hP0 h
  obtain ⟨p, hp, hpl⟩ := exists_prime_liesOver P hP0
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : H.gal H.conj = φ.cc := MulEquiv.apply_symm_apply _ _
  have hcs : H.conj H.sqd = -H.sqd := by
    rw [H.gal_sqd H.conj, h2]
    simp [Frame.cc, c0]
  by_cases hpd : p = H.d
  · haveI : P.LiesOver (span {(H.d : ℤ)}) := by rw [← hpd]; exact hpl
    have h3 := (inertia_d H P H.conj).mp h
    rw [h2] at h3
    rcases h3 with h3 | h3
    · exact cc_ne_one h3
    · have h4 := congrArg (fun g : φ.GG => ((g.1.1 : ℤˣ) : ℤ)) h3
      simp [Frame.cc, Frame.iod, c0] at h4
  · haveI := hpl
    have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
    exact Formalism.FrobeniusOrbits.Inertia.sqrt_fixed H.hyp.2.1 hd4 hp hpd P H.conj H.sqd_sq hcs h

end Formalism.HC.Der

end
