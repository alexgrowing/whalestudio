import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem card_eq_pow_finrank {F F' : Type} [Field F] [Field F'] [Finite F'] (m : Module F F') :
    Nat.card F' = Nat.card F ^ @Module.finrank F F' _ _ m := by
  letI := m
  exact Module.natCard_eq_pow_finrank

private theorem finrank_module_unique {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F'] (m₁ m₂ : Module F F') :
    @Module.finrank F F' _ _ m₁ = @Module.finrank F F' _ _ m₂ :=
  Nat.pow_right_injective (Finite.one_lt_card (α := F))
    ((card_eq_pow_finrank m₁).symm.trans (card_eq_pow_finrank m₂))

theorem UpperTheory.Gal.InertialTypesAlt.stepInert :
    FinTrace → StableOf → ResEmbCompat → ResDeg → LiftOk → JDEq → ∀ P₀, KillsOn P₀ → StepAt P₀ Not := by
  intro hFT hSt hRE hRD hLO hJD P₀ hK K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hl n hn π P hW A Θ hΘ v w hs hu e e' he he'
    τ τ' hτ hτ' a hPa hL
  obtain ⟨hOk, hq, hna, hMeets⟩ := hL
  obtain ⟨r, j, hr, hj, hje⟩ := hRE K M Ω A v w e e' he he'
  letI := r.toAlgebra
  obtain ⟨hfr, s, hsf⟩ := hRD K M hl v w hs hu
  have hfr' : @Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule = Module.finrank K M :=
    (finrank_module_unique _ _).trans hfr
  have hl' : (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule).Prime := by
    rw [hfr']
    exact hl
  let ι : AlgebraicClosure 𝓀[v.adicCompletion K] →ₐ[𝓀[v.adicCompletion K]] AlgebraicClosure 𝓀[w.1.adicCompletion M] :=
    { j.toRingHom with
      commutes' := fun x => by
        show j (algebraMap _ _ x) = _
        rw [hj x, IsScalarTower.algebraMap_apply 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M]
          (AlgebraicClosure 𝓀[w.1.adicCompletion M]) x]
        rfl }
  let θ' : AlgebraicClosure 𝓀[w.1.adicCompletion M] →* ℂ := Θ.comp e'.toMonoidHom
  have hθ' : Inj θ' := fun x y hx hy h =>
    e'.injective (hΘ _ _ (fun h0 => hx (e'.injective (by simpa using h0)))
      (fun h0 => hy (e'.injective (by simpa using h0))) h)
  have hpull : pullθ ι θ' = Θ.comp e.toMonoidHom := by
    ext x
    show Θ (e' (j x)) = Θ (e x)
    rw [hje]
  rw [← hpull] at hMeets
  subst hna
  have hlift := hLO a _ hl' hOk
  refine ⟨a.lift (@Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] _ _ Algebra.toModule),
    Relation.ReflTransGen.single ⟨_, hl', rfl⟩, hlift.1, ?_, hlift.2.symm, ?_⟩
  · show a.q ^ _ = _
    rw [hq]
    exact (card_eq_pow_finrank _).symm
  · intro hz
    have hf : IsCl fun g => star (JD (pullθ ι θ') a.D a.L a.rk g) := fun x y => by
      show star _ = star _
      rw [(hJD _ (pullθ ι θ')).2.2 a.D a.L a.rk x y]
    have hTr := hFT K M hl a.rk hn π P (hSt K M hl a.rk hn π P hW).1 hW v w hs hu τ τ' hτ hτ' hr s hsf _ hf hMeets
    have hstar : ∀ δ, shLift s (fun g => star (JD (pullθ ι θ') a.D a.L a.rk g)) δ =
        star (shLift s (JD (pullθ ι θ') a.D a.L a.rk) δ) := fun δ => by
      unfold shLift
      split_ifs <;> simp
    haveI : FiniteDimensional ℂ (fixed τ'.ρ (KOne (w.1.adicCompletion M) (Fin a.rk))) :=
      (UpperTheory.Zero.LLC.Pr.adm _ _ _ _ τ'.smooth τ'.irred).2 _ GlobalTheory.StepData.isOpen_KOne
        (levelPre_bot (k := w.1.adicCompletion M) (n := Fin a.rk) ▸ isCompact_levelPre ⊥)
    refine hTr ?_
    simp only [hstar]
    exact hK _ _ s hl' hsf ι θ' hθ' a hPa hOk hq _ (levelZero τ'.ρ) hz
