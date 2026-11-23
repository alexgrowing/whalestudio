import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem bijective_appLE_of_le_opensRange {Y Y' : Scheme.{0}} (e : Y' ⟶ Y) [IsOpenImmersion e]
    {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens} (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (e.appLE V V' h).hom := by
  obtain rfl : V' = e ⁻¹ᵁ V := le_antisymm h h'
  have := e.isIso_app V hV
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (e.app V)

theorem SecOn.pullLE_bijective_of_le_opensRange {Y Y' : Scheme.{0}} (M : LB Y) (e : Y' ⟶ Y)
    [IsOpenImmersion e] {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens}
    (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (SecOn.pullLE M e V V' h) := by
  have hb (i : M.ι) : Function.Bijective (e.appLE (V ⊓ M.U i) (V' ⊓ (M.pull e).U fun _ => i)
      ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))).hom :=
    bijective_appLE_of_le_opensRange e (inf_le_left.trans hV) _
      (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
  refine ⟨fun s t hst => GlobalTheory.LB.sec_ext fun i => (hb i).1 ?_, fun t => ?_⟩
  · exact (SecOn.coord_pullLE e h s fun _ => i).symm.trans
      ((congrArg (GlobalTheory.LB.coord · fun _ => i) hst).trans (SecOn.coord_pullLE e h t fun _ => i))
  · choose a ha using fun i => (hb i).2 (GlobalTheory.LB.coord t fun _ => i)
    refine ⟨GlobalTheory.LB.mkSec a fun i j => ?_, GlobalTheory.LB.sec_ext fun j =>
      (SecOn.coord_pullLE e h _ j).trans (ha (j PUnit.unit))⟩
    have e₁ : V' ⊓ (M.pull e).U (fun _ => i) ⊓ (M.pull e).U (fun _ => j) ≤
        e ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
      inf_le_inf ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))
        (GlobalTheory.LB.pull_U_le (L := M) e fun _ => j)
    refine (bijective_appLE_of_le_opensRange e (inf_le_left.trans (inf_le_left.trans hV)) e₁
      (inf_le_inf (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
        (GlobalTheory.LB.pull_U (L := M) e fun _ => j).ge)).1 ?_
    have := GlobalTheory.LB.coord_mem t (fun _ => i) (fun _ => j)
    rw [← ha i, ← ha j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    exact this.trans (congrArg (· * _) (GlobalTheory.LB.resG_pull_g (L := M) e (fun _ => i) (fun _ => j) _))

theorem cechLB_pull_iso_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (Y' : Scheme.{0}) (e : Y' ⟶ Y) [IsOpenImmersion e] (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → (∀ i, D i ≤ e.opensRange) → Nonempty (cechLB (e ≫ f) (M.pull e) (fun i => e ⁻¹ᵁ D i) ≅ cechLB f M D) := by
  intro R _ Y f M Y' e _ κ _ _ D _ hD
  have w : e ≫ f = (e ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  let φ : secCube f M D ⟶ secCube (e ≫ f) (M.pull e) fun i => e ⁻¹ᵁ D i :=
    GlobalTheory.Cube.homMk (fun s => secCubePull M D w s) fun h x => secCubePull_res D w h x
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ fun s ⟨i, hi⟩ =>
    SecOn.pullLE_bijective_of_le_opensRange M e ((biInf_le D hi).trans (hD i))
      (preimage_biInf D e s).ge (preimage_biInf D e s).le
  exact ⟨(asIso (cechComplexMap φ)).symm⟩

end GlobalTheory.AbLaw
