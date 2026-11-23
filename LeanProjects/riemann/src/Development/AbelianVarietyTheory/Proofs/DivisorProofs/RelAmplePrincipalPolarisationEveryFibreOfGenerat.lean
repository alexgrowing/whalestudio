import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianProperUniformisedWhereTrivialisationsGeneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleKernelTrivialOfSameImagePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointPolarisedFibreUniformisedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PolFibre

theorem generic_fibre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) :
    IsProper (pullback.snd G.hom (jK R)) ∧
      RelAmple ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) ∧
      KTriv ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  have hiso := isGrpPullback_of_iso U.gen
  have hLG : U.LG.L.IsLB := U.LG.isLB
  obtain ⟨w, hw⟩ : LBIso (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left) := by
    obtain ⟨w, hw⟩ := U.ext
    exact LBIso.symm ⟨w, hw⟩
  have hpw := (isGen_iff w).1 hw
  have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
  have := A.isAb.proper
  refine ⟨?_, relAmple_pull hiso.1 A.isLB (pull_isLB hLG _) hpw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hiso A.isLB (pull_isLB hLG _) hpw A.ktriv⟩
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  rw [← e]
  infer_instance

theorem eq_generic {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] (x : Sp K ⟶ Sp R)
    (h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥) : x (closedPoint K) = jK R (closedPoint (FractionRing R)) := by
  refine PrimeSpectrum.ext ?_
  rw [h0]
  show ⊥ = Ideal.comap (algebraMap R (FractionRing R)) (maximalIdeal (FractionRing R))
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]

theorem relAmple_kTriv_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW K _ x hx
  obtain ⟨-, hp⟩ := GlobalTheory.T.abelian_proper_uniformised_where_trivialisations_generate R hR D A G hG U W hW
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hy : x (closedPoint K) ∈ W := hx ⟨_, rfl⟩
  by_cases h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥
  · obtain ⟨h1, h2, h3⟩ := generic_fibre U
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG (FractionRing R) (jK R) h1 h2 h3 K x
      (eq_generic x h0)
  · obtain ⟨K₁, _, z, hz, h1, h2, h3⟩ := GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised R hR D A G hG U W hp (x (closedPoint K)) hy h0
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG K₁ z h1 h2 h3 K x hz.symm

end GlobalTheory.Mum.PolFibre
