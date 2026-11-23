import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Lev.fixedSs :
    UpperTheory.V.Lev.FlagPol → UpperTheory.V.Lev.FixedDvd → UpperTheory.V.Lev.FixedUnr → UpperTheory.V.Lev.FixedSs := by
  intro hP hD hU F Ω _ _ _ _ _ l _ ι n M hM m r hr w A h O _ _ _ Bw hj κ hF hst rc hrc σ hc hor
  obtain ⟨μ, hμ, hI, hG⟩ := hP F Ω l ι n M hM m r hr w A h O Bw hj κ hF hst
  have hpol : ∀ s, (rc (GlobalTheory.GalOfCusp.algNorm σ)).charPol s = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
    rw [← hc ⟨μ, hμ⟩ s]
    exact hμ s
  by_cases hw : (M : 𝓞 F) ∈ w.asIdeal
  · refine hD F Ω n M hM w hw A h rc hrc σ fun s hs => ?_
    rw [hpol]
    simp [hI _ s hs]
  · have hin : ∀ i (s : ↥(Ine (F := F) A)), μ i (ineIncl h s) = 1 := fun i s =>
      hI i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char F Ω w A h M hw s s.2)
    obtain ⟨hiw, hsp⟩ := hU F Ω n w A h rc hrc σ μ hpol hin
    have hS : GlobalTheory.SmGL.IsSpherical σ.ρ := by
      rcases hor with ⟨k, rfl⟩ | hk | hs
      · exfalso
        have hlw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := hj.mem_placesOver h
        exact hw (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hlw)
      · refine hsp fun i j => ?_
        by_contra hne
        push_neg at hne
        rcases hG i j hne with e | e
        · exact hk i j e
        · exact hk j i e
      · exact hs hiw
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS
    exact ⟨v, hv0, fun u hu => by simpa using hv ⟨u, (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M u hu).1⟩⟩
