import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPowOfPowPowEqSelfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntContinuousHomNormalizeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobAtPlaceOverPrimeStatement

noncomputable section

open ReciprocityTheory.Gal Pointwise

namespace GlobalTheory.UnrChar

theorem frob_orbit {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ)
    (hN : 0 < N) (z : k) (hz : z ^ p ^ N = z) : ∃ e : ℕ, τ z = z ^ p ^ e :=
  GlobalTheory.T.exists_ringHom_apply_eq_pow_prime_pow p τ N hN z hz

theorem exists_padic_of_compat (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n))
    (hc : ∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) :
    ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n :=
  GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' p c hc

theorem exists_normalized {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime]
    (χ : G → ℤ_[p]) (hc : Continuous χ) (hadd : ∀ g h, χ (g * h) = χ g + χ h) (g₀ : G)
    (h₀ : χ g₀ ≠ 0) : ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧
      (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 :=
  GlobalTheory.T.padicInt_continuous_hom_normalize_one p χ hc hadd g₀ h₀

theorem exists_frob_ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω)
    (hp : A.valuation (p : Ω) < 1) : ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 :=
  GlobalTheory.T.exists_frob_at_valuationSubring_over_prime A hp

theorem one_lt_pow_pow (p : ℕ) [Fact p.Prime] (n : ℕ) : 1 < p ^ p ^ n :=
  Nat.one_lt_pow (pow_pos (Fact.out : p.Prime).pos n).ne' (Fact.out : p.Prime).one_lt

theorem pow_pow_sub_one_ne_zero (p : ℕ) [Fact p.Prime] (n : ℕ) : p ^ p ^ n - 1 ≠ 0 := by
  have := one_lt_pow_pow p n; omega

theorem exists_primitive (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime]
    (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ p ^ n - 1) := by
  haveI : NeZero (p ^ p ^ n - 1) := ⟨pow_pow_sub_one_ne_zero p n⟩
  haveI : NeZero ((p ^ p ^ n - 1 : ℕ) : Ω) := inferInstance
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω _

theorem not_valuation_lt_one {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω)
    (hp : A.valuation (p : Ω) < 1) (n : ℕ) : ¬ A.valuation ((p ^ p ^ n - 1 : ℕ) : Ω) < 1 := by
  intro h
  have h1 : A.valuation ((p : Ω) ^ p ^ n) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hp (pow_pos (Fact.out : p.Prime).pos n).ne'
  have e : (1 : Ω) = (p : Ω) ^ p ^ n + -((p ^ p ^ n - 1 : ℕ) : Ω) := by
    rw [Nat.cast_sub (one_lt_pow_pow p n).le]; push_cast; ring
  have := Valuation.map_add_lt A.valuation h1 (by rw [Valuation.map_neg]; exact h)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

section main

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

def PowOn (p : ℕ) (g : Ω ≃ₐ[F] Ω) (n e : ℕ) : Prop :=
  ∀ x : Ω, x ^ (p ^ p ^ n - 1) = 1 → g x = x ^ p ^ e

theorem PowOn.mono {p : ℕ} {g : Ω ≃ₐ[F] Ω} {n₁ n₂ e : ℕ} (h : n₁ ≤ n₂) (he : PowOn p g n₂ e) :
    PowOn p g n₁ e := by
  intro x hx
  apply he
  obtain ⟨d, hd⟩ : p ^ p ^ n₁ - 1 ∣ p ^ p ^ n₂ - 1 := by
    have : p ^ p ^ n₂ = (p ^ p ^ n₁) ^ p ^ (n₂ - n₁) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' h]
    rw [this]; simpa using Nat.sub_dvd_pow_sub_pow (p ^ p ^ n₁) 1 (p ^ (n₂ - n₁))
  rw [hd, pow_mul, hx, one_pow]

theorem PowOn.mul {p : ℕ} {g h : Ω ≃ₐ[F] Ω} {n a b : ℕ} (hg : PowOn p g n a) (hh : PowOn p h n b) :
    PowOn p (g * h) n (a + b) := by
  intro x hx
  rw [AlgEquiv.mul_apply, hh x hx, hg _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]),
    ← pow_mul, pow_add, mul_comm (p ^ a)]

theorem PowOn.modEq [IsAlgClosed Ω] [CharZero Ω] {p : ℕ} [Fact p.Prime] {g : Ω ≃ₐ[F] Ω}
    {n a b : ℕ} (ha : PowOn p g n a) (hb : PowOn p g n b) : a ≡ b [MOD p ^ n] := by
  obtain ⟨ζ, hζ⟩ := exists_primitive Ω p n
  have h1 := (ha ζ hζ.pow_eq_one).symm.trans (hb ζ hζ.pow_eq_one)
  apply GlobalTheory.Cyc.modEq_of_pow_modEq_pow_sub_one p (p ^ n) a b (Fact.out : p.Prime).two_le
    (pow_pos (Fact.out : p.Prime).pos n)
  have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (pow_pow_sub_one_ne_zero p n)
  rw [hζ.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq.1 h1

variable [NumberField F] [IsAlgClosure F Ω]

theorem exists_powOn {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1)
    (g : A.decompositionSubgroup F) (n : ℕ) : ∃ e, PowOn p (g : Ω ≃ₐ[F] Ω) n e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hpp : p.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitive Ω p n
  have hm0 : p ^ p ^ n - 1 ≠ 0 := pow_pow_sub_one_ne_zero p n
  haveI : NeZero (p ^ p ^ n - 1) := ⟨hm0⟩
  have hζm : ζ ^ (p ^ p ^ n - 1) = 1 := hζ.pow_eq_one
  have hgm : ((g : Ω ≃ₐ[F] Ω) ζ) ^ (p ^ p ^ n - 1) = 1 := by rw [← map_pow, hζm, map_one]
  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp (valuation_eq_one_of_pow_eq_one A hm0 hζm).le
  let a : A := ⟨ζ, hζA⟩
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    rw [CharP.charP_iff_prime_eq_zero hpp]
    have : ((p : A)) ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff _).mpr (by simpa using hp)
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact this
  have hz : (IsLocalRing.residue A a) ^ p ^ p ^ n = IsLocalRing.residue A a := by
    rw [← map_pow]; congr 1; apply Subtype.ext
    show ζ ^ p ^ p ^ n = ζ
    rw [← Nat.sub_add_cancel (one_lt_pow_pow p n).le, pow_succ, hζm, one_mul]
  obtain ⟨e, he⟩ := frob_orbit p (MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g)
    (p ^ n) (pow_pos hpp.pos n) _ hz
  have h2 : IsLocalRing.residue A (g • a - a ^ p ^ e) = 0 := by
    rw [map_sub, IsLocalRing.ResidueField.residue_smul, map_pow, sub_eq_zero]; exact he
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  have e2 : ((g • a - a ^ p ^ e : A) : Ω) = (g : Ω ≃ₐ[F] Ω) ζ - ζ ^ p ^ e := rfl
  rw [e2] at h2
  have hgζ : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ p ^ e := by
    refine eq_of_pow_eq_one A (not_valuation_lt_one A hp n) hgm ?_ h2
    rw [← pow_mul, mul_comm, pow_mul, hζm, one_pow]
  refine ⟨e, fun x hx => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hgζ, ← pow_mul, ← pow_mul, mul_comm]

theorem main {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧
        ∃ g, χ g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hpp : p.Prime := Fact.out
  choose E hE using fun (g : A.decompositionSubgroup F) n => exists_powOn A hp g n
  have compat : ∀ (g : A.decompositionSubgroup F) n₁ n₂ (h : n₁ ≤ n₂),
      ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) ((E g n₂ : ℕ) : ZMod (p ^ n₂)) =
        ((E g n₁ : ℕ) : ZMod (p ^ n₁)) := by
    intro g n₁ n₂ h
    rw [map_natCast, ZMod.natCast_eq_natCast_iff]
    exact PowOn.modEq ((hE g n₂).mono h) (hE g n₁)
  choose χ' hχ' using fun g : A.decompositionSubgroup F =>
    exists_padic_of_compat p (fun n => ((E g n : ℕ) : ZMod (p ^ n))) (compat g)
  have key : ∀ (g : A.decompositionSubgroup F) n e, PowOn p (g : Ω ≃ₐ[F] Ω) n e →
      PadicInt.toZModPow n (χ' g) = (e : ZMod (p ^ n)) := by
    intro g n e he
    rw [hχ' g n, ZMod.natCast_eq_natCast_iff]
    exact PowOn.modEq (hE g n) he
  have hadd : ∀ g h : A.decompositionSubgroup F, χ' (g * h) = χ' g + χ' h := by
    intro g h
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [key (g * h) n _ ((hE g n).mul (hE h n)), map_add, hχ' g n, hχ' h n, Nat.cast_add]
  have hine : ∀ g : A.decompositionSubgroup F, (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ' g = 0 := by
    intro g hg
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [map_zero, key g n 0 ?_, Nat.cast_zero]
    intro x hx
    rw [pow_zero, pow_one]
    refine eq_of_pow_eq_one A (not_valuation_lt_one A hp n) (by rw [← map_pow, hx, map_one]) hx ?_
    exact hg.2 x (valuation_eq_one_of_pow_eq_one A (pow_pow_sub_one_ne_zero p n) hx).le
  have hcont : Continuous χ' := by
    refine continuous_iff_continuousAt.mpr fun g₀ => Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    obtain ⟨ζ, hζ⟩ := exists_primitive Ω p k
    haveI : NeZero (p ^ p ^ k - 1) := ⟨pow_pow_sub_one_ne_zero p k⟩
    have hV : IsOpen {g : A.decompositionSubgroup F | (g : Ω ≃ₐ[F] Ω) ζ = (g₀ : Ω ≃ₐ[F] Ω) ζ} :=
      (isOpen_setOf_apply (F := F) ζ (· = (g₀ : Ω ≃ₐ[F] Ω) ζ)).preimage continuous_subtype_val
    filter_upwards [hV.mem_nhds rfl] with g hg
    have hg' : (g : Ω ≃ₐ[F] Ω) ζ = (g₀ : Ω ≃ₐ[F] Ω) ζ := hg
    have he : PowOn p (g : Ω ≃ₐ[F] Ω) k (E g₀ k) := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      rw [map_pow, hg', ← map_pow]; exact hE g₀ k _ hx
    have h1 : PadicInt.toZModPow k (χ' g - χ' g₀) = 0 := by
      rw [map_sub, key g k _ he, hχ' g₀ k, sub_self]
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h1
    rw [dist_eq_norm]; exact lt_of_le_of_lt h1 hk
  obtain ⟨σ, hσA, q, hq1, hσ⟩ := exists_frob_ne_one (F := F) A hp
  let σ' : A.decompositionSubgroup F := ⟨σ, hσA⟩
  have hne : χ' σ' ≠ 0 := by
    intro h0
    obtain ⟨ζ, hζ⟩ := exists_primitive Ω p (q + 1)
    have hq : q + 3 ≤ p ^ p ^ (q + 1) := by
      have h1 : q + 1 < p ^ (q + 1) := Nat.lt_pow_self hpp.one_lt
      have h2 : p ^ (q + 1) < p ^ p ^ (q + 1) := Nat.pow_lt_pow_right hpp.one_lt h1
      omega
    have hk := key σ' (q + 1) _ (hE σ' (q + 1))
    rw [h0, map_zero, eq_comm, ZMod.natCast_eq_zero_iff] at hk
    obtain ⟨j, hj⟩ := hk
    have hz1 : ζ ^ p ^ p ^ (q + 1) = ζ := by
      rw [← Nat.sub_add_cancel (one_lt_pow_pow p (q + 1)).le, pow_succ, hζ.pow_eq_one, one_mul]
    have hfix : ∀ j : ℕ, ζ ^ p ^ (p ^ (q + 1) * j) = ζ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz1]
    have hσζ : σ ζ = ζ := by
      have := hE σ' (q + 1) ζ hζ.pow_eq_one
      rw [hj, hfix] at this; exact this
    have hζq : ζ = ζ ^ q := by
      refine eq_of_pow_eq_one A (not_valuation_lt_one A hp (q + 1)) hζ.pow_eq_one
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) ?_
      have := hσ ζ (valuation_eq_one_of_pow_eq_one A (pow_pow_sub_one_ne_zero p (q + 1))
        hζ.pow_eq_one).le
      rwa [hσζ] at this
    have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (pow_pow_sub_one_ne_zero p (q + 1))
    have := hfin.pow_eq_pow_iff_modEq.1 (show ζ ^ 1 = ζ ^ q by rw [pow_one]; exact hζq)
    rw [← hζ.eq_orderOf] at this
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact hq1 this.symm
  obtain ⟨ψ, hψc, hψa, hψ0, hψ1⟩ := exists_normalized p χ' hcont hadd σ' hne
  exact ⟨ψ, hψc, hψa, fun g hg => hψ0 g (hine g hg), hψ1⟩

end main

theorem unrDec : ReciprocityTheory.ChartRestriction.T2.UnrDec := by
  intro F Ω _ _ _ _ _ p _ A hp
  exact main A hp

end GlobalTheory.UnrChar
