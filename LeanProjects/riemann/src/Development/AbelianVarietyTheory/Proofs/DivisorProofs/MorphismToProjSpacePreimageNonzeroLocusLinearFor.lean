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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem comb_f {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ} (g : X ⟶ Sp R) (c : Fin n → R)
    (t : Fin n → H.Sec) (k : H.ι) :
    (∑ j, GlobalTheory.AbLaw.cst g ⊤ (c j) • t j).f k = ∑ j, GlobalTheory.AbLaw.cst g (H.U k) (c j) * (t j).f k := by
  rw [GlobalTheory.LinChange.sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]

theorem secPull_comb_f {R : Type} [CommRing R] {X Y : Scheme.{0}} {L : LB X} {n : ℕ} (p : X ⟶ Sp R)
    (c : Fin n → R) (t : Fin n → L.Sec) (φ : Y ⟶ X) (q : (L.pull φ).ι) :
    (GlobalTheory.Cartier.secPull (∑ j, GlobalTheory.AbLaw.cst p ⊤ (c j) • t j) φ).f q =
      ∑ j, GlobalTheory.AbLaw.cst (φ ≫ p) ((L.pull φ).U q) (c j) * (GlobalTheory.Cartier.secPull (t j) φ).f q := by
  have hc : ∀ (U : X.Opens) (r : R),
      (φ.app U).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (φ ≫ p) (φ ⁻¹ᵁ U) r := fun U r => by
    rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.LinChange.appLE_cst p φ le_rfl r
  dsimp only [GlobalTheory.Cartier.secPull]
  rw [comb_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hc, GlobalTheory.LinChange.resG_cst]

end GlobalTheory.SpanVA

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in

theorem GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  intro R _ X f H m N s t a hH ht hst i
  rw [← GlobalTheory.Cartier.nonzeroLocus_secPull]
  refine GlobalTheory.Cartier.SecMaps.nonzeroLocus_eq (pull_isLB (GlobalTheory.ProjSpace.O1_isLB R N) _) hH
    (w := GlobalTheory.ProjSpace.toProjIso f t ht) ?_
  rintro ⟨k, q⟩
  have hc := fun j => GlobalTheory.ProjSpace.secMaps_toProjIso f t ht j (k, q)
  change resG X _ ((s i).f k) = _ * resG X _ ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a i) (GlobalTheory.ProjSpace.toProj f t ht)).f q)
  rw [GlobalTheory.SpanVA.lin]
  rw [hst i, GlobalTheory.SpanVA.comb_f, GlobalTheory.SpanVA.secPull_comb_f, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst, hc j, GlobalTheory.ProjSpace.toProj_str]
  ring
