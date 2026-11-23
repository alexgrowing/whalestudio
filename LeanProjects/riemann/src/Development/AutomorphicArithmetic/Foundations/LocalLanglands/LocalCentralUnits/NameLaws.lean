import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GreenRegularCharacters
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PairCheckThreeTwo

noncomputable section

open Polynomial GlobalTheory.GLq

namespace UpperTheory.Zero.LLC

private theorem exists_elt {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = n) :
    ∃ y : Gn g n, Irreducible (y : Mt g n).charpoly ∧ aeval (z : K) (y : Mt g n).charpoly = 0 := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hn)
  have hint : IsIntegral (ZMod g) (z : K) := IsIntegral.of_finite (ZMod g) (z : K)
  have hdim : (Algebra.adjoin.powerBasis hint).dim = n := hz
  have hmin : minpoly (ZMod g) (Algebra.adjoin.powerBasis hint).gen = minpoly (ZMod g) (z : K) := by
    have h := minpoly.algHom_eq (Algebra.adjoin (ZMod g) {(z : K)}).val Subtype.val_injective
      (Algebra.adjoin.powerBasis hint).gen
    exact h.symm
  have hchar : (Matrix.reindex (finCongr hdim) (finCongr hdim)
      (Algebra.leftMulMatrix (Algebra.adjoin.powerBasis hint).basis
        (Algebra.adjoin.powerBasis hint).gen)).charpoly = minpoly (ZMod g) (z : K) := by
    rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, hmin]
  have hdet : IsUnit (Matrix.reindex (finCongr hdim) (finCongr hdim)
      (Algebra.leftMulMatrix (Algebra.adjoin.powerBasis hint).basis
        (Algebra.adjoin.powerBasis hint).gen)).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_eq_sign_charpoly_coeff, hchar]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    exact minpoly.coeff_zero_ne_zero hint z.ne_zero
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hchar]
    exact minpoly.irreducible hint
  · rw [IsUnit.unit_spec, hchar]
    exact minpoly.aeval _ _

private theorem pow_period {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) : θ ^ g ^ n = θ := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hn)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [@Module.card_eq_pow_finrank (ZMod g) K _ _ _ _ _, ZMod.card, hK]
  ext z
  rw [MonoidHom.pow_apply, ← map_pow]
  congr 2
  ext
  rw [Units.val_pow_eq_pow_val, ← hc, FiniteField.pow_card]

private theorem pow_add_mul {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (m k : ℕ) : θ ^ g ^ (m + n * k) = θ ^ g ^ m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + n * (k + 1) = (m + n * k) + n by ring, pow_add, pow_mul, pow_period hn hK, ih]

private theorem pow_mod {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (m : ℕ) : θ ^ g ^ (m % n) = θ ^ g ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  exact (pow_add_mul hn hK θ _ _).symm

private theorem regular_pow {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) {θ : Kˣ →* ℂˣ} (hθ : GlobalTheory.Published.IsRegularChar g n θ) (j : ℕ) :
    GlobalTheory.Published.IsRegularChar g n (θ ^ g ^ j) := by
  intro a b ha hb hab
  apply hθ a b ha hb
  have e1 : ∀ c, θ ^ g ^ c = ((θ ^ g ^ j) ^ g ^ c) ^ g ^ (n * j - j) := by
    intro c
    rw [← pow_mul, ← pow_mul, ← pow_add_mul hn hK θ c j]
    congr 1
    simp only [← pow_add]
    congr 1
    have hj : j ≤ n * j := Nat.le_mul_of_pos_left j hn
    generalize n * j = t at hj ⊢
    omega
  rw [e1 a, e1 b, hab]

theorem nameLaws :
    UpperTheory.Zero.LLC.NameLaws := by
  intro g _ n hn K _ _ hK
  obtain ⟨τF, hτ1, hτ2, hτ3⟩ := PositivityTheory.Stage1.PM.greenRegularCharacters g n hn K hK
  have hnames : ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
      ∀ τ : FDRep ℂ (Gn g n), τ.character = τF θ → Names g n θ τ := by
    intro θ hθ τ hτ y hy z hz
    rw [hτ]
    exact (hτ1 θ hθ).2.2 y hy z hz
  have huniq : ∀ (τ : FDRep ℂ (Gn g n)) (θ θ' : Kˣ →* ℂˣ), GlobalTheory.Published.IsRegularChar g n θ →
      GlobalTheory.Published.IsRegularChar g n θ' → Names g n θ τ → Names g n θ' τ → ∃ j < n, θ' = θ ^ g ^ j := by
    intro τ θ θ' hθ hθ' h1 h2
    refine (UpperTheory.Zero.LLC.pin g n hn K hK θ hθ).2 θ' hθ' fun z hz => ?_
    obtain ⟨y, hy, hyz⟩ := exists_elt hn hK z hz
    have e := (h1 y hy z hyz).symm.trans (h2 y hy z hyz)
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) e
  have hchar : ∀ (τ : FDRep ℂ (Gn g n)) (θ : Kˣ →* ℂˣ), GlobalTheory.GLq.IsCusp τ.character →
      GlobalTheory.Published.IsRegularChar g n θ → Names g n θ τ → τ.character = τF θ := by
    intro τ θ hc hθ hN
    obtain ⟨θ₁, hθ₁, h1⟩ := hτ3 _ hc
    obtain ⟨i, hi, hi'⟩ := huniq τ θ θ₁ hθ hθ₁ hN (hnames θ₁ hθ₁ τ h1)
    rw [h1]
    exact ((hτ2 θ θ₁ hθ hθ₁).mpr ⟨i, hi, hi'⟩).symm
  refine ⟨fun τ hc => ?_, huniq, fun τ τ' θ j hc hc' hθ hN hN' => ?_, fun K' _ _ e τ θ' => ?_⟩
  · obtain ⟨θ, hθ, h⟩ := hτ3 _ hc
    exact ⟨θ, hθ, hnames θ hθ τ h⟩
  · rw [hchar τ' _ hc' (regular_pow hn hK hθ j) hN', hchar τ θ hc hθ hN, ← pow_mod hn hK θ j]
    exact ((hτ2 θ _ hθ (regular_pow hn hK hθ (j % n))).mpr ⟨j % n, Nat.mod_lt _ hn, rfl⟩).symm
  · have hf : ∀ x : ZMod g, e (algebraMap (ZMod g) K x) = algebraMap (ZMod g) K' x := fun x =>
      RingHom.congr_fun
        (RingHom.ext_zmod (e.toRingHom.comp (algebraMap (ZMod g) K)) (algebraMap (ZMod g) K')) x
    let eA : K ≃ₐ[ZMod g] K' := AlgEquiv.ofRingEquiv hf
    refine ⟨fun hN y hy z hz => ?_, fun hreg a b ha hb hab => hreg a b ha hb ?_⟩
    · have hz' : aeval ((Units.map (e.toRingHom : K →* K') z : K'ˣ) : K') (y : Mt g n).charpoly = 0 := by
        have h := Polynomial.aeval_algHom_apply eA.toAlgHom (z : K) (y : Mt g n).charpoly
        rw [hz, map_zero] at h
        exact h
      rw [hN y hy _ hz']
      simp [map_pow]
    · ext z
      obtain ⟨w, rfl⟩ : ∃ w, Units.map (e.toRingHom : K →* K') w = z :=
        ⟨Units.map (e.symm.toRingHom : K' →* K) z, by ext; simp⟩
      have h := congrArg (fun χ : Kˣ →* ℂˣ => χ w) hab
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply] at h ⊢
      exact congrArg (fun u : ℂˣ => (u : ℂ)) h

end UpperTheory.Zero.LLC

end
