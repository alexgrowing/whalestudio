import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGtStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforwardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedAltBis

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GroundTheory.Arith.SchemeCoh
namespace GlobalTheory.CompanionTheory.GE

theorem step_integral {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (IH : ∀ J' : X.IdealSheafData, J < J' → Statement I J') : Statement I J := by
  intro E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  letI : J.subscheme.Over (Spec (.of A)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of A))⟩
  have h1 : IsSeparated (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : IsSeparated (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h2 : LocallyOfFiniteType (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : LocallyOfFiniteType (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h3 : QuasiCompact (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : QuasiCompact (J.subschemeι ≫ (X ↘ Spec (.of A))))
  obtain ⟨N, Y, i, O, ψ, W, hi, hψ, hcomm, hW, hiso⟩ := GlobalTheory.T.exists_chow_cover_integral (A := A) (X := J.subscheme)
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩
  have hZ : Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := GlobalTheory.T.formal_existence_projective_open I hI i hi O
  have hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = ((O : Scheme.{0}) ↘ Spec (.of A)) := by
    change (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = O.ι ≫ i ≫ ProjSpace.toSpecBase A N
    rw [hcomm, Category.assoc]
    rfl
  obtain ⟨D, c, J', hDq, hDP, hc, hJ, hkill⟩ := GlobalTheory.T.formal_existence_proper_pushforward I hI J hZ ψ hψ hover W hW hiso hE hS hK hP
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP D hDq c hc
  exact halg (IH J' hJ _ (GlobalTheory.T.coherent_subobject_coherent hE D hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J' D S c' hkill) hP') hDP

theorem statement_bot {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    (X : Scheme.{0}) [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] :
    Statement I (⊥ : X.IdealSheafData) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hwf : WellFoundedGT X.IdealSheafData := GlobalTheory.T.ideal_sheaf_well_founded_gt
  refine WellFoundedGT.induction (motive := fun J : X.IdealSheafData => Statement I J) ⊥ ?_
  intro J IH
  by_cases hJ : J = ⊤
  · subst hJ
    exact GlobalTheory.T.formal_existence_top_ideal I
  rcases GlobalTheory.T.noetherian_ideal_integral_or_split J hJ with h | ⟨J₁, J₂, h₁, h₂, hm⟩
  · exact step_integral I hI J IH
  · exact GlobalTheory.T.formal_existence_product_ideal I J J₁ J₂ hm (IH _ h₁) (IH _ h₂)

theorem geClosed : GEClosed :=
  GlobalTheory.T.geClosed_of_statement_bot fun _ _ _ I hI X _ _ _ _ => statement_bot I hI X

end GlobalTheory.CompanionTheory.GE
