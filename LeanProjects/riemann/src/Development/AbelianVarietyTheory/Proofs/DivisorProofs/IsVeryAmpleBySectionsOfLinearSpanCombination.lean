import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusSecPullLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpacePreimageNonzeroLocusLinearForStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceEqLinearProjectionCompStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem iSup_nonzeroLocus_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {H : LB X} {m N : ℕ}
    {s : Fin (m + 1) → H.Sec} {t : Fin (N + 1) → H.Sec} {a : Matrix (Fin (m + 1)) (Fin (N + 1)) R}
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) :
    ⨆ j, nonzeroLocus (t j) = ⊤ := by
  refine top_unique fun y _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨k, hk⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  by_contra hne
  have hnu : ∀ j, ¬ IsUnit (X.presheaf.germ (H.U k) y hk ((t j).f k)) := fun j hu =>
    hne (Opens.mem_iSup.2 ⟨j, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).2 ((X.mem_basicOpen _ y hk).2 hu)⟩)
  have hu := (X.mem_basicOpen _ y hk).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).1 hi)
  have e : (s i).f k = ∑ j, GlobalTheory.AbLaw.cst f (H.U k) (a i j) * (t j).f k := by
    rw [hst i, GlobalTheory.LinChange.sum_f]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]
  rw [e, map_sum] at hu
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => ?_) hu
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu j))

theorem isClosedImmersion_of_comp_open {X P Q S : Scheme.{0}} (U : P.Opens) (φ : X ⟶ U.toScheme)
    (ψ : U.toScheme ⟶ Q) (p : P ⟶ S) (q : Q ⟶ S) (hc : IsClosedImmersion (φ ≫ ψ)) (hp : IsSeparated p)
    (hq : ψ ≫ q = U.ι ≫ p) (hpr : IsProper (φ ≫ U.ι ≫ p)) : IsClosedImmersion (φ ≫ U.ι) := by
  have : IsSeparated (ψ ≫ q) := by rw [hq]; infer_instance
  have : IsSeparated ψ := IsSeparated.of_comp ψ q
  have : IsClosedImmersion φ := IsClosedImmersion.of_comp φ ψ
  have : IsProper ((φ ≫ U.ι) ≫ p) := by rw [Category.assoc]; exact hpr
  have : IsProper (φ ≫ U.ι) := IsProper.of_comp _ p
  exact IsClosedImmersion.of_isPreimmersion _ (φ ≫ U.ι).isClosedMap.isClosed_range

end GlobalTheory.SpanVA

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in

theorem GlobalTheory.veryAmpleBy_of_span : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → GlobalTheory.AbLaw.VeryAmpleBy f H t := by
  intro R _ X f H m N s t a hH hv hst
  obtain ⟨hs, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hv
  have ht := GlobalTheory.SpanVA.iSup_nonzeroLocus_of_span f hs hst
  refine (GlobalTheory.ProjSpace.veryAmpleBy_iff f t).2 ⟨ht, ?_⟩
  have hpre : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤ := by
    rw [GlobalTheory.SpanVA.dom, Scheme.Hom.preimage_iSup]
    simp only [GlobalTheory.T.morphismToProjSpace_preimage_nonzeroLocus_linearForm R X f H m N s t a hH ht hst]
    exact hs
  have e := GlobalTheory.T.morphismToProjSpace_eq_linearProjection_comp R X f H m N s t a hH hs ht hst hpre
  rw [← GlobalTheory.SpanVA.liftDom_fac a _ hpre]
  have hp : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.SpanVA.isClosedImmersion_of_comp_open _ _ (GlobalTheory.SpanVA.proj a) (PSpace.str R N) (PSpace.str R m)
    (e ▸ hci) hp (GlobalTheory.ProjSpace.toProj_str _ _ _) ?_
  rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  exact GlobalTheory.isProper_of_veryAmpleBy hv
