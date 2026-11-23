import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Th.temper :
    Af.Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub F n), (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → ∃ t : ℝ, ((rc (algNorm σ)).lpTw t).tempered := by
  intro hP F Ω _ _ _ _ _ _ n hn π hreg ⟨χ, hpol⟩ w A h rc hrc σ hσ
  obtain ⟨l, hlp, hl⟩ : ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := by
    by_cases h2 : ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal
    · refine ⟨3, Nat.prime_three, fun h3 => w.isPrime.ne_top ?_⟩
      rw [Ideal.eq_top_iff_one]
      have e : ((3 : ℕ) : 𝓞 F) - ((2 : ℕ) : 𝓞 F) = 1 := by push_cast; ring
      rw [← e]
      exact w.asIdeal.sub_mem h3 h2
    · exact ⟨2, Nat.prime_two, h2⟩
  have : Fact l.Prime := ⟨hlp⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal F Ω l ι n hn π χ hreg hpol
  obtain ⟨x, hx, ht⟩ := H.pure w hl A h
  exact ⟨(wt : ℝ) / 2, IsWDOf.unique hl hx (H.away w hl A h rc hrc σ hσ) ▸ ht⟩
