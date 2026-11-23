import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem coordAt_id_pullbackSections {B Y : Scheme.{0}} {M : B.Modules} {r : ℕ} (hM : IsVB M r) (π : Y ⟶ B)
    {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ B) (hx : ⊤ ≤ x ⁻¹ᵁ V)
    (y : Sp K ⟶ Y) (w : y ≫ π = x) {W : Y.Opens} (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W)
    (s : Γ((Scheme.Modules.pullback π).obj M, W)) :
    coordAt hM x hf (𝟙 (Sp K)) hx le_rfl
      (((Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M).app ⊤
        (QCoh.pullbackSections y _ hy s)) = coordAt hM π hf y hWV hy s := by
  haveI := hM.isQuasicoherent
  have key : ∀ t : Γ(M, V),
      ((Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M).app ⊤
        (QCoh.pullbackSections y _ hy (QCoh.pullbackSections π M hWV t)) = QCoh.pullbackSections x M hx t := by
    intro t
    subst w
    rw [← Vert.DivPull.pullbackComp_inv_app y π M hWV hy hx t, QCoh.app_app, Iso.inv_hom_id_app_assoc]
    rfl
  set c := ((hf.pullback π).basis hWV).repr s with hc
  have hs : s = ∑ b, c b • QCoh.pullbackSections π M hWV (f b) := by
    conv_lhs => rw [← ((hf.pullback π).basis hWV).sum_repr s]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [IsFrame.basis_apply]
    simp only [Twist.resM, QCoh.res_pullbackSections, hc]
  have h2 : ((Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M).app ⊤
        (QCoh.pullbackSections y _ hy s) = ∑ b, (y.appLE W ⊤ hy).hom (c b) • (hf.pullback x).basis hx b := by
    rw [hs]
    simp only [map_sum, QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, key, IsFrame.basis_apply,
      Twist.resM, QCoh.res_pullbackSections]
  funext b
  simp only [coordAt]
  rw [h2, Module.Basis.repr_sum_self, ← hc]
  simp [TangentOrigin.evalPt, Scheme.Hom.appLE]

theorem flagMat_of_stepIso : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (x : Sp K ⟶ B), ⊤ ≤ x ⁻¹ᵁ V → ∀ (fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r) (A : Matrix (Fin r) (Fin r) K), FlagMat hM x fl' hf (𝟙 (Sp K)) A → ∀ (y : Sp K ⟶ Y) (w : y ≫ π = x), StepIso π fl fl' y w → FlagMat hM π fl hf y A := by
  intro B Y M r hM π fl V f hf K _ x hx fl' A hA y w hS
  refine ⟨hA.1, fun k W hWV t hy => ?_⟩
  obtain ⟨e, he⟩ := hS k
  obtain ⟨cf, h1, h2⟩ := hA.2 k ⊤ hx (e.hom.app ⊤ (QCoh.pullbackSections y _ hy t)) le_rfl
  refine ⟨cf, h1, ?_⟩
  rw [← h2, QCoh.app_app, he, ← QCoh.app_app, QCoh.pullback_map_app_pullbackSections]
  exact (coordAt_id_pullbackSections hM π hf x hx y w hWV hy _).symm

end GlobalTheory.FlagCls

end
