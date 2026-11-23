import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackGluedQuotientKernelPairOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedQuotientMapFiniteFlatSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfChartsSurjectiveImageStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem quotGlobal_holds : QuotGlobal := by
  intro S _ A _ H _ i hA hi hm hf hfl
  have := hA.comm
  choose B instB q hq using GlobalTheory.T.exists_abelianQuotient_affineCover S A H i hA hi hm hf hfl
  have hfin : ∀ j, IsFinite (q j).left := fun j => (hq j).2.2.1
  have hflat : ∀ j, Flat (q j).left := fun j => (hq j).2.2.2.1
  have hsurj : ∀ j, Surjective (q j).left := fun j => (hq j).2.2.2.2.1
  have hqc : ∀ j, QuasiCompact (q j).left := fun j => by have := hfin j; infer_instance
  have hsq : ∀ j, _ := fun j => (hq j).2.2.2.2.2
  obtain ⟨b, hb1, hb2, hchar⟩ := GlobalTheory.T.exists_local_quotient_transition_isomorphisms S S.affineCover A H i B q hflat hsurj hqc hsq
  have hcoc := GlobalTheory.T.local_quotient_transition_cocycle S S.affineCover A H i B q b hflat hsurj hqc hb1 hchar
  obtain ⟨G0, F, ψ, hψ, hψ2⟩ := GlobalTheory.CocycleGlue.exists_glue (fun j => S.affineCover.X j) (fun j => (B j).left)
    (fun j => S.affineCover.f j) (fun j => inferInstance) (fun j => (B j).hom)
    (fun j k => pullback ((B j).hom ≫ S.affineCover.f j) (S.affineCover.f k)) (fun j k => pullback.fst _ _) b
    (fun j k => by rw [hb1]; exact IsPullback.of_hasPullback _ _) hb2 hcoc
  obtain ⟨Qm, hQF, hQm⟩ := GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients S S.affineCover A H i B q b G0 F ψ hchar (fun j k => (hψ2 j k).w)
    (fun j => (hψ j).w)
  let G : Over S := Over.mk F
  let Q : A ⟶ G := Over.homMk Qm hQF
  have hpb : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q :=
    GlobalTheory.T.isPullback_gluedQuotient_kernelPair_of_cover S S.affineCover A H G i Q B ψ q hψ hQm hsq
  obtain ⟨hQfin, hQfl, hQs⟩ := GlobalTheory.T.gluedQuotientMap_finite_flat_surjective S S.affineCover A G Q B ψ q hψ hQm hfin hflat hsurj
  have : IsCommMonObj A := hA.comm
  have : IsMonHom i := hi
  have : QuasiCompact Q.left := inferInstance
  obtain ⟨instG, hcomm, hhom, -⟩ := GlobalTheory.AbelianQuotient.exists_grpObj i Q hpb
  exact ⟨G, instG, Q, GlobalTheory.T.isAbelianScheme_of_charts_surjective_image S S.affineCover A G Q B ψ hA hcomm hQs hψ (fun j => (hq j).1), hhom, hQfin, hQfl, hQs, hpb⟩

end GlobalTheory.IwLevel
