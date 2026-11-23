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

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on appLE_resG appLE_appLE appLE_of_eq)

theorem lin_f {R : Type} [CommRing R] {m N : ℕ} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (j : Fin (m + 1))
    (i : Fin (N + 1)) :
    (lin a j).f i = ∑ n, GlobalTheory.AbLaw.cst (PSpace.str R N) (chart R N i) (a j n) * GlobalTheory.ProjSpace.ratio R N i n := by
  refine (GlobalTheory.LinChange.sum_f (H := O1 R N) _ i).trans (Finset.sum_congr rfl fun n _ => ?_)
  refine (GlobalTheory.LB.smul_f (L := O1 R N) _ _ i).trans ?_
  rw [GlobalTheory.LinChange.resG_cst]
  exact congrArg (_ * ·) (coord_f R N n i)

end GlobalTheory.SpanVA

theorem GlobalTheory.SpanVA.toProj_eq_liftDom_proj : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  intro R _ X f H m N s t a _ hs ht hst h
  have hg : GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N = f := by
    rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N)
    (GlobalTheory.SpanVA.iSup_nonzeroLocus_secPull_lin a) (GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h)
    (t := s) hs ?_
  · rw [hg] at e
    exact e
  intro z
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i :=
    inf_le_left.trans (GlobalTheory.ProjSpace.toProj_preimage_chart f t ht i).ge
  have hk : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ⁻¹ᵁ
      ((GlobalTheory.ProjSpace.O1 R N).pull (GlobalTheory.SpanVA.dom a).ι).U (fun _ => i) := by
    refine hW.trans (le_of_eq ?_)
    erw [GlobalTheory.Cartier.pull_U]
    rw [← Scheme.Hom.comp_preimage, GlobalTheory.SpanVA.liftDom_fac]
    rfl
  refine ⟨nonzeroLocus (t i) ⊓ H.U l, ⟨hi, hl⟩, fun _ => i, hk, l, inf_le_right, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X inf_le_right ((t i).f l),
    fun j => ?_⟩
  have key : ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a j) (GlobalTheory.SpanVA.dom a).ι).f (fun _ => i)) =
      ((GlobalTheory.ProjSpace.toProj f t ht).appLE (GlobalTheory.ProjSpace.chart R N i) _ hW).hom ((GlobalTheory.SpanVA.lin a j).f i) := by
    show ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG _ _ (((GlobalTheory.SpanVA.dom a).ι.app _).hom ((GlobalTheory.SpanVA.lin a j).f i))) = _
    rw [GlobalTheory.ProjSpace.appLE_resG, Scheme.Hom.app_eq_appLE, GlobalTheory.ProjSpace.appLE_appLE]
    exact congrArg (fun ψ => ψ.hom ((GlobalTheory.SpanVA.lin a j).f i))
      (GlobalTheory.ProjSpace.appLE_of_eq (GlobalTheory.SpanVA.liftDom_fac a _ h) (GlobalTheory.ProjSpace.chart R N i) _ _ hW)
  rw [key, GlobalTheory.SpanVA.lin_f, map_sum, hst j, GlobalTheory.LinChange.sum_f, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst]
  erw [GlobalTheory.LinChange.appLE_cst (PSpace.str R N) (GlobalTheory.ProjSpace.toProj f t ht) hW (a j n)]
  rw [GlobalTheory.ProjSpace.toProj_str]
  change _ = _ * (_ * GlobalTheory.ProjSpace.pullRatio (GlobalTheory.ProjSpace.toProj f t ht) _ i hW n)
  rw [GlobalTheory.ProjSpace.pullRatio_toProj_on, GlobalTheory.ProjSpace.secRatio_on (t i) (t n) l inf_le_left inf_le_right]
  ring
