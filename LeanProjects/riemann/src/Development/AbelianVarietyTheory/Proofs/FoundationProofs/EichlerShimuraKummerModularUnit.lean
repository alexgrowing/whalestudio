import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosureProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunctionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonLthPowerReductionAlmostAllPrimesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGaloisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateFieldStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendentalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOneStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.ESFun

theorem val_lt_one_iff {F : Type} [Field F] (A : ValuationSubring F) (x : F) :
    A.valuation x < 1 ↔ x = 0 ∨ ¬ A.valuation x⁻¹ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : 0 < A.valuation x := by
      rw [zero_lt_iff]; simpa using hx
    rw [map_inv₀, inv_le_one₀ h0]; simp [hx]

theorem val_eq_one_iff {F : Type} [Field F] (A : ValuationSubring F) (x : F) :
    A.valuation x = 1 ↔ x ≠ 0 ∧ A.valuation x ≤ 1 ∧ A.valuation x⁻¹ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : 0 < A.valuation x := by
      rw [zero_lt_iff]; simpa using hx
    rw [map_inv₀, inv_le_one₀ h0]; simp only [ne_eq, hx, not_false_eq_true, true_and]
    exact le_antisymm_iff

theorem comap_le_one {L K : Type} [Field L] [Field K] (φ : L →+* K) (W : ValuationSubring K) (x : L) :
    (W.comap φ).valuation x ≤ 1 ↔ W.valuation (φ x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]

theorem comap_lt_one {L K : Type} [Field L] [Field K] (φ : L →+* K) (W : ValuationSubring K) (x : L) :
    (W.comap φ).valuation x < 1 ↔ W.valuation (φ x) < 1 := by
  rw [val_lt_one_iff, val_lt_one_iff, comap_le_one, map_inv₀, map_eq_zero]

theorem comap_eq_one {L K : Type} [Field L] [Field K] (φ : L →+* K) (W : ValuationSubring K) (x : L) :
    (W.comap φ).valuation x = 1 ↔ W.valuation (φ x) = 1 := by
  rw [val_eq_one_iff, val_eq_one_iff, comap_le_one, comap_le_one, map_inv₀, ne_eq, ne_eq, map_eq_zero]

theorem frob_symm {Ω : Type} [Field Ω] [Algebra ℚ Ω] (q : ℕ) (hq : 0 < q) (s : Ω ≃ₐ[ℚ] Ω)
    (V : ValuationSubring Ω) (hs : ∀ x ∈ V, s x ∈ V ∧ V.valuation (s x - x ^ q) < 1) :
    ∀ x ∈ V, s.symm x ∈ V := by
  intro x hx
  by_contra hy
  have hy0 : s.symm x ≠ 0 := by intro h; apply hy; rw [h]; exact V.zero_mem
  have h1 : ¬ V.valuation (s.symm x) ≤ 1 := by rwa [V.valuation_le_one_iff]
  have hpos : 0 < V.valuation (s.symm x) := by rw [zero_lt_iff]; simpa using hy0
  have hyinv : V.valuation (s.symm x)⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ hpos]; exact not_le.1 h1
  have hyV : (s.symm x)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 hyinv.le
  obtain ⟨_, h2⟩ := hs _ hyV
  have h3 : V.valuation ((s.symm x)⁻¹ ^ q) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hyinv hq.ne'
  have h4 : V.valuation (s (s.symm x)⁻¹) < 1 := by
    have e : s (s.symm x)⁻¹ = (s (s.symm x)⁻¹ - (s.symm x)⁻¹ ^ q) + (s.symm x)⁻¹ ^ q := by ring
    rw [e]; exact Valuation.map_add_lt _ h2 h3
  rw [map_inv₀, AlgEquiv.apply_symm_apply, map_inv₀] at h4
  have hx0 : x ≠ 0 := by intro h; apply hy0; simp [h]
  have hxpos : 0 < V.valuation x := by rw [zero_lt_iff]; simpa using hx0
  rw [inv_lt_one₀ hxpos] at h4
  exact absurd ((V.valuation_le_one_iff _).2 hx) (not_le.2 h4)

theorem lev_sl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (σ : SL(2, ℤ)) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.sl (ofSL σ) f) = X.sl (ofSL σ) f := by
  intro γ hγ
  have hn : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma M := (CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ σ
  have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
  rw [← X.sl_mul, ← map_mul, e, map_mul, X.sl_mul, hf _ hn]

end GlobalTheory.KZ.ESFun

namespace GlobalTheory.KZ.ESFun
theorem levKron : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := GlobalTheory.T.kroneckerHeckeProduct_invariant_principal_level
theorem levGal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := GlobalTheory.T.towerGaloisAction_preserves_gammaLevel
theorem unMap : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m → (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := GlobalTheory.T.modularFunctionTower_unitGroup_stable_slash_galois
theorem red1 : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := GlobalTheory.T.kroneckerRatio_reduces_to_const_mod_valuation
theorem finLev : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧ ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := GlobalTheory.T.exists_levelFunctions_intermediateField
theorem jTr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := GlobalTheory.T.towerJInvariant_transcendental
theorem rootLift : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K] [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 → ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := GlobalTheory.T.exists_rootOfUnity_close_of_pow_reduces_one
end GlobalTheory.KZ.ESFun

namespace GlobalTheory.KZ.ESFun

theorem prod_mem_Un {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) {ι : Type}
    (t : Finset ι) (u : ι → X.Kˣ) (h : ∀ i ∈ t, u i ∈ X.Un m) : (∏ i ∈ t, u i) ∈ X.Un m := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using UnClosure.one_mem X m
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact UnClosure.mul_mem X m _ _ (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem eichler_shimura_kummer : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l : ℕ) [Fact l.Prime] (M n : ℕ) (f : X.Kˣ), 0 < M → l ∣ M → f ∈ X.Un (l ^ n) → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∃ g : X.Kˣ, (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  intro Ω _ _ _ ε X hε hj l hl M n f hM hlM hfU hfM
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert (IsAlgClosure.isAlgebraic : Algebra.IsAlgebraic ℚ Ω)
    exact Subsingleton.elim _ _
  have hl' : l.Prime := hl.out
  have hlpos : 0 < l := hl'.pos
  obtain ⟨L, hL, hjL, hfd⟩ := finLev ε X hε hj M hM
  have htr : Transcendental Ω (⟨X.jK, hjL⟩ : L) := by
    intro halg
    exact jTr X (by simpa using halg.algHom L.val)
  obtain ⟨R, hR⟩ := GlobalTheory.T.modularTower_units_finite_mod_powers_at_level ε X hε hj M (l ^ n) hM (pow_pos hlpos n)
  have key : ∀ r : X.Kˣ, ∃ S : Finset ℕ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (r : X.K) = r) →
      (¬ ∃ c : Ω, c ≠ 0 ∧ ∃ u : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (u : X.K) = u) ∧
        (r : X.K) = algebraMap Ω X.K c * (u : X.K) ^ (l ^ n)) →
      ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits →
      ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) →
      (∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) →
        W.valuation (Polynomial.aeval X.jK P) = 1) →
      ∀ h : X.K, h ∈ L → h ≠ 0 → ∀ C : Ω, C ≠ 0 →
        ¬ W.valuation (algebraMap Ω X.K C * (r : X.K) * h ^ (l ^ n) - 1) < 1 := by
    intro r
    by_cases hr : (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (r : X.K) = r) ∧
        ¬ ∃ c : Ω, c ≠ 0 ∧ ∃ u : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (u : X.K) = u) ∧
          (r : X.K) = algebraMap Ω X.K c * (u : X.K) ^ (l ^ n)
    swap
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
    obtain ⟨hrM, hng⟩ := hr
    have hrL : (r : X.K) ∈ L := (hL _).2 hrM
    let Pa : ℕ → Prop := fun a => ∃ c : Ω, c ≠ 0 ∧ ∃ z : L, z ≠ 0 ∧
      (r : X.K) = algebraMap Ω X.K c * ((z : L) : X.K) ^ (l ^ a)
    have hP0 : Pa 0 := ⟨1, one_ne_zero, ⟨r, hrL⟩, by
        intro h; exact r.ne_zero (by simpa using congrArg Subtype.val h), by simp⟩
    have hPa : Pa (Nat.findGreatest Pa n) := Nat.findGreatest_spec (Nat.zero_le n) hP0
    have han : Nat.findGreatest Pa n ≤ n := Nat.findGreatest_le n
    have hmax : ¬ Pa (Nat.findGreatest Pa n + 1) ∨ n < Nat.findGreatest Pa n + 1 := by
      by_cases h : Nat.findGreatest Pa n + 1 ≤ n
      · exact Or.inl (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h)
      · exact Or.inr (by omega)
    generalize Nat.findGreatest Pa n = a at hPa han hmax
    obtain ⟨c1, hc1, z, hz, hrz⟩ := hPa
    have hlt : a < n := by
      rcases lt_or_eq_of_le han with h | h
      · exact h
      · exfalso; apply hng
        refine ⟨c1, hc1, Units.mk0 ((z : L) : X.K) (by simpa using hz), ?_, ?_⟩
        · exact (hL _).1 z.2
        · rw [← h]; simpa using hrz
    have hzl : ∀ u : L, u ^ l ≠ z := by
      intro u hu
      have hu0 : u ≠ 0 := by
        rintro rfl; exact hz (by rw [← hu, zero_pow hl'.ne_zero])
      have hPa1 : Pa (a + 1) := ⟨c1, hc1, u, hu0, by
        rw [hrz, ← hu]; push_cast; rw [← pow_mul, pow_succ, mul_comm l]⟩
      rcases hmax with h | h
      · exact h hPa1
      · omega
    obtain ⟨S, hS⟩ := GlobalTheory.T.nonLthPower_reduction_almost_all_primes (F := Ω) (K := L) (⟨X.jK, hjL⟩ : L) htr hfd l hl' z hzl
    refine ⟨S, fun _ _ q hq hqS V hqV W hWa hWb h hhL hh0 C hC hv => ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, n = a + k + 1 := ⟨n - a - 1, by omega⟩
    have e1 : l ^ n = l ^ (k + 1) * l ^ a := by rw [← pow_add]; congr 1; omega
    let φ : L →+* X.K := algebraMap L X.K
    have hWLa : ∀ b : Ω, algebraMap Ω L b ∈ W.comap φ ↔ b ∈ V := fun b => by
      rw [ValuationSubring.mem_comap]; exact hWa b
    have hWLb : ∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) →
        (W.comap φ).valuation (Polynomial.aeval (⟨X.jK, hjL⟩ : L) P) = 1 := by
      intro P h1 h2
      rw [comap_eq_one]
      have e2 : φ (Polynomial.aeval (⟨X.jK, hjL⟩ : L) P) = Polynomial.aeval X.jK P := by
        have := Polynomial.aeval_algHom_apply L.val (⟨X.jK, hjL⟩ : L) P
        show ((Polynomial.aeval (⟨X.jK, hjL⟩ : L) P : L) : X.K) = _
        simpa using this.symm
      rw [e2]; exact hWb P h1 h2
    obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (C * c1) (pow_pos hlpos a)
    have hx : W.valuation ((algebraMap Ω X.K e * ((z : L) : X.K) * h ^ (l ^ (k + 1))) ^ (l ^ a) - 1) < 1 := by
      have e3 : (algebraMap Ω X.K e * ((z : L) : X.K) * h ^ (l ^ (k + 1))) ^ (l ^ a)
          = algebraMap Ω X.K C * (r : X.K) * h ^ (l ^ n) := by
        rw [e1, hrz, mul_pow, mul_pow, ← map_pow, he, ← pow_mul, map_mul]; ring
      rw [e3]; exact hv
    obtain ⟨ζ, hζ, hv2⟩ := rootLift (Ω := Ω) W _ (l ^ a) (pow_pos hlpos a) hx
    obtain ⟨e₁, he₁⟩ := IsAlgClosed.exists_pow_nat_eq e hlpos
    have he₁0 : e₁ ≠ 0 := by
      rintro rfl
      rw [zero_pow hl'.ne_zero] at he₁
      rw [← he₁, zero_pow (pow_pos hlpos a).ne'] at he
      exact mul_ne_zero hC hc1 he.symm
    let H : L := ⟨algebraMap Ω X.K e₁ * h ^ (l ^ k), L.mul_mem (L.algebraMap_mem e₁) (pow_mem hhL _)⟩
    have hH0 : H ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      simp only [H, IntermediateField.coe_zero] at this
      rcases mul_eq_zero.1 this with h5 | h5
      · exact he₁0 (by simpa using h5)
      · exact hh0 (pow_eq_zero_iff (pow_pos hlpos k).ne' |>.1 h5)
    have hζ1 : V.valuation ζ = 1 :=
      UnClosure.val_eq_one_of_pow V ζ (l ^ a) (pow_pos hlpos a) (by rw [hζ, map_one])
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow (pow_pos hlpos a).ne'] at hζ; exact zero_ne_one hζ
    have hζV : ζ ∈ V := (V.valuation_le_one_iff _).1 hζ1.le
    have hζV' : ζ⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, hζ1, inv_one])
    apply hS q hq hqS V hqV (W.comap φ) ⟨hWLa, fun P h1 h2 => hWLb P h1 (by obtain ⟨i, hi⟩ := h2; exact ⟨i, by tauto⟩)⟩ H ζ hH0 hζ0 hζV hζV'
    rw [comap_lt_one]
    convert hv2 using 2
    simp only [φ, H, map_sub, map_mul, map_pow]
    show ((z : L) : X.K) * (algebraMap Ω X.K e₁ * h ^ (l ^ k)) ^ l - algebraMap Ω X.K ζ = _
    rw [mul_pow, ← map_pow, he₁, ← pow_mul, ← pow_succ]; ring
  choose Sr hSr using key
  obtain ⟨SE, hSE⟩ := red1 ε X hε hj M f hM hfM
  refine ⟨SE ∪ M.primeFactors ∪ R.biUnion Sr, ?_⟩
  intro q hq hqS s hs σ hσ
  simp only [Finset.mem_union, Finset.mem_biUnion, not_or, not_exists, not_and] at hqS
  obtain ⟨⟨hqE, hqM⟩, hqR⟩ := hqS
  have hcop : Nat.Coprime q M := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hd; exact hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  obtain ⟨V, hqV, hsV⟩ := hs
  have hsymm := frob_symm q hq.pos s V hsV
  have hV' : ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1 :=
    fun x hx => ⟨(hsV x hx).1, hsymm x hx, (hsV x hx).2⟩
  obtain ⟨W, hWa, hWb, hWc⟩ := GlobalTheory.T.exists_valuationSubring_gauss_modularFunction ε X hε hj q hq V hqV
  obtain ⟨κ, hκ, hred⟩ := hSE q hq hqE V s hqV hV' σ hσ W hWa hWc
  have hU := unMap ε X hε hj (l ^ n) f hfU
  have hne : ∀ g : GQ, X.sl g (f : X.K) ≠ 0 := fun g => (map_ne_zero (X.sl g)).2 f.ne_zero
  have hσU : Units.mk0 _ (hne (ofSL σ)) ∈ X.Un (l ^ n) := hU.1 _ _ rfl
  have hne2 : X.gal s.symm (X.sl (ofSL σ) (f : X.K)) ≠ 0 := (map_ne_zero (X.gal s.symm)).2 (hne _)
  have hne3 : X.gal s (f : X.K) ≠ 0 := (map_ne_zero (X.gal s)).2 f.ne_zero
  let PU : X.Kˣ := (∏ j ∈ Finset.range q, Units.mk0 _ (hne (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]))) *
    Units.mk0 _ (hne (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])))
  let BU : X.Kˣ := Units.mk0 _ hne3 * (Units.mk0 _ hne2) ^ q
  have hPU : PU ∈ X.Un (l ^ n) :=
    UnClosure.mul_mem X _ _ _ (prod_mem_Un X _ _ _ fun j _ => hU.1 _ _ rfl) (hU.1 _ _ rfl)
  have hBU : BU ∈ X.Un (l ^ n) :=
    UnClosure.mul_mem X _ _ _ (hU.2 _ _ rfl)
      (UnClosure.pow_mem X _ _ _ ((unMap ε X hε hj (l ^ n) _ hσU).2 s.symm _ rfl))
  have hPv : (PU : X.K) = (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) := by
    simp only [PU, Units.val_mul, Units.coe_prod, Units.val_mk0]
  have hBv : (BU : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q := by
    simp only [BU, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  let rU : X.Kˣ := PU * BU⁻¹
  have hrUn : rU ∈ X.Un (l ^ n) := UnClosure.mul_mem X _ _ _ hPU (UnClosure.inv_mem X _ _ hBU)
  have hrv : (rU : X.K) = (PU : X.K) / (BU : X.K) := by
    simp only [rU, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have hrM : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (rU : X.K) = rU := by
    intro γ hγ
    rw [hrv, hPv, hBv, map_div₀, levKron X M q σ (f : X.K) hM hq hcop hfM hσ γ hγ, map_mul, map_pow,
      levGal X M s (f : X.K) hM hfM γ hγ, levGal X M s.symm _ hM (lev_sl X M σ _ hfM) γ hγ]
  obtain ⟨r0, hr0R, g, hgM, c, hc, hrep⟩ := hR rU hrUn hrM
  have hr0M : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (r0 : X.K) = r0 := by
    intro γ hγ
    have e : (r0 : X.K) = (rU : X.K) / ((g : X.K) ^ (l ^ n) * algebraMap Ω X.K c) := by
      have hc0 : algebraMap Ω X.K c ≠ 0 := by simpa using hc
      rw [hrep, mul_assoc, mul_div_assoc, div_self (mul_ne_zero (pow_ne_zero _ g.ne_zero) hc0), mul_one]
    rw [e, map_div₀, map_mul, map_pow, AlgEquiv.commutes, hrM γ hγ, hgM γ hγ]
  have hB0 : (BU : X.K) ≠ 0 := BU.ne_zero
  by_cases hgood : ∃ c' : Ω, c' ≠ 0 ∧ ∃ u : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (u : X.K) = u) ∧
      (r0 : X.K) = algebraMap Ω X.K c' * (u : X.K) ^ (l ^ n)
  · obtain ⟨c', hc', u, -, hr0u⟩ := hgood
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c' * c) (pow_pos hlpos n)
    have hd0 : d ≠ 0 := by
      rintro rfl; rw [zero_pow (pow_pos hlpos n).ne'] at hd; exact mul_ne_zero hc' hc hd.symm
    refine ⟨Units.mk0 (algebraMap Ω X.K d * (u : X.K) * (g : X.K))
      (mul_ne_zero (mul_ne_zero (by simpa using hd0) u.ne_zero) g.ne_zero), ?_⟩
    rw [← hPv, ← hBv]
    calc (PU : X.K) = (BU : X.K) * ((PU : X.K) / (BU : X.K)) := (mul_div_cancel₀ _ hB0).symm
      _ = _ := by
        rw [← hrv, hrep, hr0u, Units.val_mk0, mul_pow, mul_pow, ← map_pow, hd, map_mul]; ring
  · exfalso
    refine hSr r0 hr0M hgood q hq (hqR r0 hr0R) V hqV W hWa (fun P h1 h2 => hWb P h1 (by obtain ⟨i, hi⟩ := h2; exact ⟨i, by tauto⟩)) (g : X.K) ((hL _).2 hgM) g.ne_zero (κ * c)
      (mul_ne_zero hκ hc) ?_
    have e : algebraMap Ω X.K (κ * c) * (r0 : X.K) * (g : X.K) ^ (l ^ n) =
        algebraMap Ω X.K κ * ((PU : X.K) / (BU : X.K)) := by
      rw [← hrv, hrep, map_mul]; ring
    rw [e, hPv, hBv, ← mul_div_assoc]
    exact hred

end GlobalTheory.KZ.ESFun
