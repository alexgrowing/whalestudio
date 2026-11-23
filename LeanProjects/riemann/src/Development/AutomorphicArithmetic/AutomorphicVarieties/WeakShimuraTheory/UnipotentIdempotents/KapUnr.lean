import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.kapUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ P.tL.ker) ∧ (∀ A, Raw.Away D.S A → Ine (F := T.L) A ≤ P.κ.ker) ∧ ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, P.κ g ^ m = 1 := by
  intro Ω _ _ _ l _ c D T P hG
  have hK : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resLe (K_le T) g ∈ Ine (F := T.K) A :=
    fun A g hg => hg
  have hQ : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resQ T.L g ∈ Ine (F := ℚ) A :=
    fun A g hg => hg
  have ht : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.t (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.t_unr A hA (hK A g hg))
  have hb : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.β (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.β_t (P.t_unr A hA (hK A g hg)))
  have hc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.γ (resQ T.L g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.γ_ker ((places ℚ Ω l A).2.2.2 hA (hQ A g hg)))
  have hκ : ∀ g, P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := fun g => rfl
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  refine ⟨fun A hA g hg => MonoidHom.mem_ker.2 (ht A hA g hg), ?_, m, hm, ?_⟩
  · intro A hA g hg
    have hl : ¬ A.valuation (l : Ω) < 1 := hA l hG.l_mem
    rw [MonoidHom.mem_ker, hκ, MonoidHom.mem_ker.1 (P.κ₀_unr A hA (hK A g hg)), hc A hl g hg,
      hb A hl g hg]
    simp
  · intro A hA g hg
    have h0 : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    rw [hκ, hc A hA g hg, hb A hA g hg]
    simp [h0]
