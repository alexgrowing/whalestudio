import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem pullbackComp_congr_app_pullbackSections {B Y T : Scheme.{0}} (π : Y ⟶ B) (g' : T ⟶ Y) (g : T ⟶ B)
    (w : g' ≫ π = g) (E : B.Modules) {U : B.Opens} {V : Y.Opens} {V' : T.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (h : V' ≤ g' ⁻¹ᵁ V) (h' : V' ≤ g ⁻¹ᵁ U) (t : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp g' π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E).app V'
      (QCoh.pullbackSections g' _ h (QCoh.pullbackSections π E hV t)) = QCoh.pullbackSections g E h' t := by
  subst w
  rw [← Vert.DivPull.pullbackComp_inv_app g' π E hV h h' t, QCoh.app_app, Iso.inv_hom_id_app_assoc]
  rfl

theorem spans_pullCol_of_carries : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (U : B.Opens) (a : ι) (e : Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (M : Matrix (Fin (r a)) (Fin (r a)) Γ(Y, V)) (V' : T.Opens) (h : V' ≤ g' ⁻¹ᵁ V) (h' : V' ≤ g ⁻¹ᵁ U), Spans (fl a) V (pullCol π e hV M) → Spans (fl' a) V' (pullCol g e h' (M.map (g'.appLE V V' h).hom)) := by
  intro B Y T π ι r E fl g' g w fl' hC U a e V hV M V' h h' hS l
  obtain ⟨s, hs, hsι⟩ := hS l
  obtain ⟨φ, hφ⟩ := hC a l
  haveI := ((fl a).isVB l).isQuasicoherent
  refine ⟨fun j => φ.hom.app V' (QCoh.pullbackSections g' _ h (s j)), ?_, fun j => ?_⟩
  · have h1 := (hs.pullback g').res h
    simp only [Twist.resM, QCoh.res_pullbackSections] at h1
    exact h1.map_iso φ.hom
  · dsimp only
    rw [QCoh.app_app, hφ, ← QCoh.app_app, QCoh.pullback_map_app_pullbackSections, hsι j]
    simp only [pullCol, map_sum, QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, Matrix.map_apply,
      pullbackComp_congr_app_pullbackSections π g' g w (E a) hV h h']

end GlobalTheory.FlagCell
