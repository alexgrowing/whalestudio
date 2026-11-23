import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem val_lt_iff {Ω : Type} [Field Ω] {A B : ValuationSubring Ω} (g : Ω ≃+* Ω)
    (h : ∀ x, g x ∈ A ↔ x ∈ B) (y : Ω) : A.valuation (g y) < 1 ↔ B.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', h, ← map_inv₀, h, map_eq_zero_iff g g.injective]

private theorem card_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] {ι : Type} (pl : ι → ValuationSubring Ω) (ovl : ∀ v, (pl v).valuation (l : Ω) < 1)
    (cover : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃! v, ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ pl v) :
    Nat.card ι = ((Ideal.span {(l : ℤ)}).primesOver (𝓞 F)).ncard := by
  classical
  have hlp : l.Prime := hl.out
  have hplace : ∀ v, ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (pl v) w := fun v => by
    by_cases htop : pl v = ⊤
    · exact absurd (ovl v) ((places F Ω l (pl v)).2.1 htop).2
    · exact (places F Ω l (pl v)).1 htop
  choose w hw using hplace
  have huniq : ∀ {A : ValuationSubring Ω} {w₁ w₂ : HeightOneSpectrum (𝓞 F)},
      IsPlaceOver A w₁ → IsPlaceOver A w₂ → w₁ = w₂ := by
    intro A w₁ w₂ h₁ h₂
    apply HeightOneSpectrum.ext
    ext x
    rw [← h₁ x, ← h₂ x]
  have htrans : ∀ {A B : ValuationSubring Ω} (g : G F Ω), (∀ x, g x ∈ A ↔ x ∈ B) →
      ∀ u : HeightOneSpectrum (𝓞 F), IsPlaceOver A u → IsPlaceOver B u := by
    intro A B g hg u hA x
    rw [← hA x, ← val_lt_iff g.toRingEquiv hg]
    simp only [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  have hinj : Function.Injective w := by
    intro v₁ v₂ he
    have h2 : IsPlaceOver (pl v₂) (w v₁) := by rw [he]; exact hw v₂
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hw v₁) h2
    obtain ⟨v, -, hv⟩ := cover (pl v₂) (ovl v₂)
    have e1 := hv v₁ ⟨σ, fun x => by rw [← hσ]; exact ValuationSubring.smul_mem_pointwise_smul_iff⟩
    have e2 := hv v₂ ⟨1, fun x => by simp⟩
    rw [e1, e2]
  have hinj' : Function.Injective (fun v => (w v).asIdeal) :=
    fun a b h => hinj (HeightOneSpectrum.ext h)
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hlp).irreducible
  have habove : ∀ (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
      (A.valuation (l : Ω) < 1 ↔ (l : 𝓞 F) ∈ u.asIdeal) := by
    intro A u hu
    rw [(places F Ω l A).2.2.1 u hu]
    rfl
  rw [← Nat.card_range_of_injective hinj', _root_.Nat.card_coe_set_eq]
  congr 1
  ext P
  simp only [Set.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(w v).isPrime, ⟨?_⟩⟩
    have hl' : (l : 𝓞 F) ∈ (w v).asIdeal := (habove _ _ (hw v)).1 (ovl v)
    have hle : Ideal.span {(l : ℤ)} ≤ (w v).asIdeal.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under] using hl'
    exact hmax.eq_of_le (Ideal.IsPrime.under ℤ (w v).asIdeal).ne_top hle
  · rintro ⟨hP, hlies⟩
    have hl' : (l : 𝓞 F) ∈ P := by
      have : (l : ℤ) ∈ P.under ℤ := by rw [← hlies.over]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.under] using this
    have hne : P ≠ ⊥ := by
      intro hb
      rw [hb, Ideal.mem_bot] at hl'
      exact hlp.ne_zero (by exact_mod_cast hl')
    let u : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hne⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver (F := F) Ω u
    have hAl : A.valuation (l : Ω) < 1 := (habove A u hA).2 hl'
    obtain ⟨v, ⟨g, hg⟩, -⟩ := cover A hAl
    exact ⟨v, congrArg HeightOneSpectrum.asIdeal (huniq (hw v) (htrans g hg u hA))⟩

theorem UpperTheory.V.Ws.chDv :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∃ dv : ℕ, dv * Nat.card T.ι = T.d := by
  intro Ω _ _ _ l hl c D T
  haveI : IsAlgClosure T.F Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
        Algebra.IsAlgebraic.tower_top (K := ℚ) T.F }
  haveI hmax : (Ideal.span {(l : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(l : ℤ)}) (𝓞 T.F) (T.F ≃ₐ[ℚ] T.F)
  rw [IsGalois.card_aut_eq_finrank, ← card_eq l T.pl T.ovl T.cover] at h
  exact ⟨_, (mul_comm _ _).trans h⟩
