import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LocUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m n : ℕ} (h : m ∣ n)
    (hA : A.valuation (m : Ω) < 1) : A.valuation (n : Ω) < 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  have hk : A.valuation (k : Ω) ≤ 1 := by
    simpa using A.valuation_le_one (k : A)
  calc A.valuation (m : Ω) * A.valuation (k : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hk
    _ < 1 := by rwa [mul_one]

private theorem val_prod {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (S : Finset ℕ)
    (hA : A.valuation ((∏ p ∈ S, p : ℕ) : Ω) < 1) : ∃ p ∈ S, A.valuation (p : Ω) < 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hA
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Nat.cast_mul, map_mul] at hA
    by_cases hp : A.valuation (a : Ω) < 1
    · exact ⟨a, Finset.mem_insert_self a S, hp⟩
    · have h1 : A.valuation (a : Ω) = 1 :=
        le_antisymm (by simpa using A.valuation_le_one (a : A)) (not_lt.mp hp)
      rw [h1, one_mul] at hA
      obtain ⟨p, hpS, hp'⟩ := ih hA
      exact ⟨p, Finset.mem_insert_of_mem hpS, hp'⟩

private theorem vlen_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (he : e ≠ 0) (ψ : DirichletCharacter c.O N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Vlen Ω c e ψ ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ) := by
  classical
  haveI := c.dvr
  haveI := c.fin
  have hcls := Chr.clsFacts ℚ Ω N
  have hker : (Chr.cls ℚ Ω N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [Chr.dirG, hg]
  have hopen : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hker hcls.1
  have hpow : Chr.dirG ℚ Ω ψ ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow,
      pow_card_eq_one, map_one]
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω) (z : ℤ), A.valuation x < 1 →
      A.valuation (x * (z : Ω)) < 1 := by
    intro A x z hx
    rw [map_mul]
    have hz : A.valuation (z : Ω) ≤ 1 := by simpa using A.valuation_le_one (z : A)
    calc A.valuation x * A.valuation (z : Ω) ≤ A.valuation x * 1 := mul_le_mul' le_rfl hz
      _ < 1 := by rwa [mul_one]
  show Chr.VS l (l * N) e (Chr.dirG ℚ Ω ψ) ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ)
  unfold Chr.VS
  refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  simp only [Base.ShaU, Base.mem_locSel] at hx ⊢
  intro D hD
  rcases hD with ⟨A, hAS, rfl⟩ | ⟨A, rfl⟩
  · obtain ⟨p, hpS, hp⟩ := val_prod A S hAS
    by_cases hdvd : p ∣ l * N
    · exact hx (Dec A) (Or.inl ⟨A, val_dvd A hdvd hp, rfl⟩)
    · have pp := hS p hpS
      have hpl : p ≠ l := by
        rintro rfl
        exact hdvd (dvd_mul_right p N)
      have hpN : ¬ p ∣ N := fun h' => hdvd (dvd_mul_of_dvd_right h' l)
      have hN : ¬ A.valuation (N : Ω) < 1 := by
        intro hN
        have hcop : Nat.gcd p N = 1 := ((Nat.Prime.coprime_iff_not_dvd pp).2 hpN)
        have hb := Nat.gcd_eq_gcd_ab p N
        rw [hcop] at hb
        have h1 : (1 : Ω) = (p : Ω) * (Nat.gcdA p N : Ω) + (N : Ω) * (Nat.gcdB p N : Ω) := by
          have := congrArg (fun z : ℤ => (z : Ω)) hb
          push_cast at this
          exact this
        have hsum := Valuation.map_add_lt A.valuation (hint A _ (Nat.gcdA p N) hp)
          (hint A _ (Nat.gcdB p N) hN)
        rw [← h1, map_one] at hsum
        exact lt_irrefl _ hsum
      have hIne : Ine A ≤ (Chr.dirG ℚ Ω ψ).ker := le_trans (hcls.2.2.2.2 A hN) hker
      have hU : (⊤ : Subgroup (G ℚ Ω)) ⊓ Ine A ≤ ⊤ ⊓ Dec A := inf_le_inf_left _ (Ine_le_Dec A)
      have hinj := (Chr.locUnr Ω l c.O e (Fintype.card (ZMod N)ˣ) (Chr.dirG ℚ Ω ψ) he
        Fintype.card_ne_zero hopen hpow p A pp hpl hp (⊤ ⊓ Ine A) (⊤ ⊓ Dec A) hU
        (top_inf_eq _) (top_inf_eq _)).2 (inf_le_right.trans hIne)
      have h0 := hx (Ine A) (Or.inr ⟨A, rfl⟩)
      have h2 : Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) hU
          (Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (inf_le_left : ⊤ ⊓ Dec A ≤ ⊤) x) = 0 := by
        rw [Base.resU_resU]
        exact h0
      exact hinj (h2.trans (map_zero _).symm)
  · exact hx (Ine A) (Or.inr ⟨A, rfl⟩)

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaEq :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → Aut.OfCase D h e ψ → Vlen Ω c e ψ ≤ D.sha := by
  intro Ω _ _ _ h t _ l _ c e _ he _ ψ _ D hD hA
  have key : ∀ {n' p₁ m₀ : ℕ}, Aut.OfChar D e ψ n' p₁ m₀ → Vlen Ω c e ψ ≤ D.sha := by
    intro n' p₁ m₀ hc
    unfold Raw.sha
    rw [hc.e_eq, hc.psi]
    exact vlen_le Ω l c h.N e he.ne' ψ D.S hD.S_prime
  rcases hA with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact key hc
  · exact key hc
