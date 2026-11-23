import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.TriOfLines
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.KeepsGap

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J

private lemma weight_gap_ne_succ (e : ℕ) (i j : Fin 2) :
    (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≠ (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j + 1 := by
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem UpperTheory.V.Z.Keep.keeps2 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → Block η r → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ [Algebra K L] [IsScalarTower K L Ω] (W : G K Ω →* GL (Fin 2) (Qbar l)), (∀ s, (W s).val = corner (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → Z.Win.Keeps W L :=
  fun Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ C₀ k hΦ A _ _ r hO hB h1 K _ _ _ _ _ hK _ _ W hW =>
    UpperTheory.V.Z.Keep.keepsGap K L Ω l 2 N ![(e : ℤ), -(e : ℤ)] W (NeZero.one_le)
      (UpperTheory.V.Z.Keep.ordFlag2 Ω l c N e ψ η σ g₁ B M hL L Φ C₀ k hΦ A r hO hB h1 K hK W hW)
      (weight_gap_ne_succ e)
