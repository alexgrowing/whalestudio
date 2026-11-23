import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CoCoprod

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private structure SxCOb (O : Type) [CommRing O] [IsLocalRing O] : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]

attribute [local instance] SxCOb.ring SxCOb.alg SxCOb.co

theorem UpperTheory.V.Ws.sxCoprodOpt :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (T : Type) [Finite T] (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra Λ (B t)] [∀ t, IsCO Λ (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (i : A →ₐ[Λ] R) (j : ∀ t, B t →ₐ[Λ] R), ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (fa : A →ₐ[Λ] R') (f : ∀ t, B t →ₐ[Λ] R'), ∃! g : R →ₐ[Λ] R', g.comp i = fa ∧ ∀ t, g.comp (j t) = f t := by
  intro Λ _ _ _ _ T _ A _ _ _ B _ _ _
  let F : Option T → Type := fun o => Option.elim o A B
  letI iR : ∀ o, CommRing (F o) := fun o =>
    match o with
    | none => (inferInstance : CommRing A)
    | some t => (inferInstance : CommRing (B t))
  letI iA : ∀ o, Algebra Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : Algebra Λ A)
    | some t => (inferInstance : Algebra Λ (B t))
  have iC : ∀ o, IsCO Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : IsCO Λ A)
    | some t => (inferInstance : IsCO Λ (B t))
  obtain ⟨R, iRR, iAl, iCO, j, hj⟩ := UpperTheory.V.CA.co_coprod Λ (Option T) F
  refine ⟨R, iRR, iAl, iCO, (j none : A →ₐ[Λ] R), fun t => (j (some t) : B t →ₐ[Λ] R), ?_⟩
  intro R' _ _ _ fa f
  let h : ∀ o, F o →ₐ[Λ] R' := fun o =>
    match o with
    | none => fa
    | some t => f t
  obtain ⟨g, hg, hu⟩ := hj R' h
  refine ⟨g, ⟨hg none, fun t => hg (some t)⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  apply hu
  intro o
  cases o with
  | none => exact h1
  | some t => exact h2 t
