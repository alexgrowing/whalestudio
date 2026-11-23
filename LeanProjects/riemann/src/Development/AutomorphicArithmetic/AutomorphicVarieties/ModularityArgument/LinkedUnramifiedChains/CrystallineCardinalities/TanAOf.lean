import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.BoxUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LinkOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.FiniteCocyclesOfFiniteH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LeOf2

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.Z.J

namespace UpperTheory.V.J

def UnitOfP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
    (ξ : R.S.R →ₐ[c₁.O] c₁.O) (r : G L Ω →* GL (Fin 3) (Qbar l)),
    (∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1) →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 = (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1) →
    ∀ v : Φ.V, PotCrysAt r (k.pl v) → ∀ i j,
    (∀ g : Φ.Gv v, (ξ (R.S.ρ.ψ v i g).val).1 = (ξ (R.S.ρ.ψ v j g).val).1 * (cycBar ℚ Ω l (k.j v g).1 : Qbar l)) →
    ∃ i' : Fin 2, UnitAt (R.S.ρ.map (ξ : R.S.R →+* c₁.O)) v i'

theorem tanA_of (hP : GC.Hypotheses₂) (hD : DegEq) (hU : UnitOfP) : TanA := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f R ξ r hr _ hI v hc i j hij
  obtain ⟨i', hu⟩ := hU Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f R ξ r hr hI v hc i j hij
  obtain ⟨cw, hcw, S, K, π, ι', A, pl, e', cc, hF⟩ := linkOf Ω l c.O η _ σ g₁ B M hL.atl L Φ k _ f R.C₀ R.ok
    (hD Ω l ι c N e ψ η σ g₁ B M hL L Φ k v).1
  obtain ⟨δ, hδ, δ', hδ', hi⟩ := Z.J.tan l c₁.O (Φ.ext f) R.C₀ R.ok R.T.lne cw hcw
    (gwlOf hP l _ _ _ Ω S K π ι' A pl e' cc hF) (fun w => leOf2 hP l _ { Φ.ext f with cw := cw } _ Ω S K π ι' A pl e' cc hF w) R.S ξ v i' hu
  exact ⟨δ, hδ.1, δ', hδ'.1, hδ.2, hδ'.2, hi⟩

end UpperTheory.V.J

end
