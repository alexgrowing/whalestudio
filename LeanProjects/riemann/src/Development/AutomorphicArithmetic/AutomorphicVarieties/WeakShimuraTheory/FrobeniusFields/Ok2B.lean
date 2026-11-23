import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.ok2B :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → (∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL) ∧ (∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1) ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l hl c D hD X T hT
  obtain ⟨hpq, -, hxi, -, -⟩ := away D hD
  obtain ⟨-, -, -, -, -, hrb, -, -, -⟩ := barFacts D hD
  have hH : ∀ g : G T.F Ω, resQ T.F g ∈ X.H := fun g => hT.1 ▸ resQ_mem T.F g
  refine ⟨fun A g hg => ?_, fun A hA g hg h => ?_, ?_, fun A hA g hg => ?_⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    change resQ T.F g ∈ T.K.fixingSubgroup
    rw [hT.2]
    by_cases hp : A.valuation (X.p : Ω) < 1
    · have hp' : ¬ A.valuation (X.p' : Ω) < 1 := fun h =>
        X.hη'.nm (hpq A _ _ X.hη.prime X.hη'.prime hp h ▸ Finset.mem_insert_self _ _)
      exact (X.mem_H.1 (hH g)).2.1.trans (X.hη'.unr A hp' hg')
    · exact X.hη.unr A hp hg'
  · exact X.kap.kb A hA _ ((resQ_Ine T.F A g).1 hg) ((hrb _).1 h).2 (X.mem_H.1 (hH g)).2.2
  · obtain ⟨m, hm, h⟩ := X.kap.kc
    exact ⟨m, hm, fun g hg => h _ ((resQ_cyc T.F g).trans hg) (X.mem_H.1 (hH g)).2.2⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    have h3 : ¬ A.valuation (X.p₃ : Ω) < 1 := fun h =>
      X.hφ.nm (hpq A _ _ hl.out X.hφ.prime hA h ▸ hD.l_mem)
    have h1 : D.ξ (resQ T.F g) = 1 := hxi A hA hg'
    have h2 : X.φ (resQ T.F g) = 1 := X.hφ.unr A h3 hg'
    refine (hrb _).2 ⟨?_, ?_⟩
    · rw [Raw.bar, h1, Units.val_one, map_one]
    · rw [(X.mem_H.1 (hH g)).1, h2, Units.val_one, Int.cast_one]
