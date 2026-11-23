import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverEmbeddingClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfClosedFibreEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnifStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CoverFin

theorem semiAbelian_of_pull {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} {G' : Over T} [GrpObj G']
    [IsCommMonObj G'] {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, hbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  haveI := hbc
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem isLocalHom_of_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B)
    (h : (maximalIdeal B).comap φ = maximalIdeal A) : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hn
  have : a ∈ (maximalIdeal B).comap φ := by rw [h]; exact (mem_maximalIdeal a).2 hn
  exact (mem_maximalIdeal _).1 this ha

end GlobalTheory.Mum.CoverFin

open GlobalTheory.Mum.CoverFin

theorem GlobalTheory.Mum.hasFin_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), Nonempty (LabCover D) → HasFin D := by
  intro R _ _ _ hB D ⟨C⟩
  obtain ⟨R', _, _, _, ρ, D', C', E, hρ, hD', hθ⟩ := GlobalTheory.T.exists_labelledCover_embedding_closedFibre R hB D C
  obtain ⟨G, _, _, P, β, hG, hβ, hL⟩ := GlobalTheory.T.semiAbelian_descends_of_closedFibre_embedding R' hρ.1 C'.toModif C'.G C'.semi C'.P E hθ
  haveI : IsNoetherianRing R' := hρ.1.1
  haveI : CharZero R := hB.2
  haveI : CharZero R' := charZero_of_injective_ringHom hρ.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
  have hloc : IsLocalHom φ := isLocalHom_of_comap φ hm
  haveI : IsDiscreteValuationRing V := hV.1
  let fφ : FractionRing R' →+* FractionRing V :=
    IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)
  have hfφ : ∀ r, fφ (algebraMap R' _ r) = algebraMap V _ (φ r) := fun r => IsLocalization.map_eq _ _
  haveI : IsProper C'.π := C'.proper
  obtain ⟨ξ, -, hξ⟩ := val_exists C'.π (spMap fφ ≫ C'.gp) (spMap φ) (by
    rw [Category.assoc, C'.gp_π]
    show spMap fφ ≫ spMap (algebraMap R' (FractionRing R')) = spMap (algebraMap V (FractionRing V)) ≫ spMap φ
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    exact RingHom.ext fun r => hfφ r)
  obtain ⟨W', _, _, _, io, G'', _, _, β', D'', A'', U'', hD'', hW', hio, hfin, hβ', hL', -⟩ :=
    C'.trait V hV φ ξ hφ hloc hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hcomp : IsGrpPullback G'' G (spMap (io.comp φ)) (β' ≫ β) :=
    (hβ'.comp hβ).congr (by rw [Category.assoc, hξ, spMap_comp]) rfl
  have h₂ : LBIso (C'.P.L.L.pull β') (P.L.L.pull (β' ≫ β)) :=
    LBIso.chartPull (chartPullPull C'.P.L.L β') (chartPullSame P.L.L _ _ _ β' fun _ => rfl) hL
  have hLc : LBIso U''.LG.L (P.L.L.pull (β' ≫ β)) :=
    LBIso.trans U''.LG.isLB (pull_isLB C'.P.L.isLB β') (pull_isLB P.L.isLB _) hL' h₂
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hρ₁, hD₁, hβ₁, -⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif R' ⟨hρ.1, inferInstance⟩ D' G P hG W' hW' (io.comp φ) (hio.comp hφ) inferInstance G'' (β' ≫ β) D'' A'' U''
      hcomp hLc ⟨hD''⟩
  exact GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt_trans R R' ρ hρ D D' hD'
    ⟨R₁, _, _, _, ρ₁, D₁, hρ₁, hD₁, G₁, _, _, A₁, semiAbelian_of_pull hβ₁ hG, ⟨U₁⟩⟩
