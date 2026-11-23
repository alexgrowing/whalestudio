import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem isCommMonObj_of_isGrpPullback [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

theorem isAbelianScheme_of_isGrpPullback [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G)
    (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' where
  comm := have := hG.comm; isCommMonObj_of_isGrpPullback h
  smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth
  proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper
  geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected

theorem relAmple_restrict (h : IsPullback φ G'.hom G.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) (hA : Out.RelAmple G L) (V : S.Opens) (hV : IsAffineOpen V) :
    Out.RelAmple (Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (G'.hom ∣_ (f ⁻¹ᵁ V)) G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict G'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullPull L' _ _ rfl)
      (chartPullSame L (fun _ : PUnit => (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => φ) (fun _ => 1) _ fun _ => rfl) e
  exact relAmple_pull (A' := Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) H hL (pull_isLB hL' _)
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

theorem pol_pull_of_relAmple_local
    (hloc : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
        Out.RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → Out.RelAmple A L) :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') := by
  intro S S' G G' _ _ f φ L L' hL hL' hG h e
  have hG' := isAbelianScheme_of_isGrpPullback hG h
  have := hG'.proper
  refine ⟨hG', fun hA => hloc S' G' L' hL' inferInstance inferInstance fun s => ?_, fun hK => ?_⟩
  · obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 hL hL' e hA V hV⟩
  · obtain ⟨w, hw⟩ := e
    exact kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.PolPull
