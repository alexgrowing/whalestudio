import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

private theorem isPlaceOver_under {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {A : ValuationSubring Ω} {w : Plc L} (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 (Lp L))) := by
  intro x
  exact h (algebraMap _ (𝓞 L) x)

theorem UpperTheory.V.Z.Sym.Pl.linkUnr :
    UpperTheory.V.Z.Sym.Pl.LinkUnr := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k
  haveI : IsAlgClosure L Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
        Algebra.IsAlgebraic.tower_top (K := ℚ) L }
  refine ⟨UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω fun A _ _ g hg => (k.mem_range_resP g).2 (k.unr A ⟨hg, (Pr.toUpl Ω L g).2⟩), fun w hw => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hM : A.valuation (M : Ω) < 1 := (Pr.natCast_place hA M).2 hw
  exact UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω A _ (isPlaceOver_under hA)
    (fun g hg => (k.mem_range_resP g).2 (k.split A hM ⟨hg, (Pr.toUpl Ω L g).2⟩)) w rfl
