import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open Formalism.GaloisCohomology UpperTheory.V UpperTheory.Top

private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv)
    (hψ : PsiEven e ψ) : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
  have h1 : cycZ ℚ Ω l σ = -1 := h.cyc (E := ℚ)
  have h2 : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have h3 : chiO ℚ Ω l O σ = -1 := by
    ext
    simp [chiO, h1]
  have h4 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : Oˣ) : O) = (-1) ^ e * ψ (-1) := by
    simp [Chr.Psi, Chr.dirG, h2, h3]
  have h5 : ((-1 : O) ^ e) * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Units.ext_iff, h4, Units.val_one, hψ, h5]

theorem UpperTheory.V.Ws.xi2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → (∃ n : ℕ, D.ξ ^ 2 ^ n = 1) ∧ (∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker) ∧ ∀ σ : G ℚ Ω, IsCC σ → D.Psi σ = 1 := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, h, t, e, ψ, -, -, -, hψ, -, hO⟩ := hD
  obtain ⟨he, hp, -, _, ξ', ξ₀, -, -, h0, hξ⟩ := hO
  generalize h.nII l ψ = n at ξ' hξ
  have h1 : ξ₀ = 1 := orderOf_eq_one_iff.1 h0
  have h2 : ∀ σ, D.ξ σ = ξ'.toUnitHom (Chr.cls ℚ Ω (2 ^ n) σ) := by
    intro σ
    rw [hξ, MonoidHom.mul_apply, h1]
    have : Chr.cls ℚ Ω 1 σ = 1 := Subsingleton.elim _ _
    simp [Chr.dirG, this]
  refine ⟨⟨n, ?_⟩, fun A hA σ hσ => ?_, fun σ hσ => ?_⟩
  · ext1 σ
    rw [MonoidHom.pow_apply, h2, ← map_pow, MonoidHom.one_apply]
    have h3 : Chr.cls ℚ Ω (2 ^ n) σ ^ 2 ^ n = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      refine orderOf_dvd_card.trans ?_
      rw [ZMod.card_units_eq_totient]
      rcases n with _ | n
      · simp
      · rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp [pow_succ]
    rw [h3, map_one]
  · have h3 : ¬ A.valuation ((2 ^ n : ℕ) : Ω) < 1 := by
      have h4 := hA 2 (Finset.mem_singleton_self 2)
      rw [Nat.cast_pow, map_pow]
      exact not_lt.2 (one_le_pow₀ (not_lt.1 h4))
    have h4 : Chr.cls ℚ Ω (2 ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (2 ^ n)).2.2.2.2 A h3 hσ
    rw [MonoidHom.mem_ker, h2, h4, map_one]
  · rw [Raw.Psi, he, hp]
    exact psi_cc Ω l ψ e hσ (h.mem_X.1 hψ).2
