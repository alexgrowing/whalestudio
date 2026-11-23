import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIdFlagPieceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPiecePullbackCompIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackPieceIsoFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalArithModelGenericPointMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedMetricOfIsometricStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagTransport

theorem exists_iso {B Y₀ Y : Scheme.{0}} (π₀ : Y₀ ⟶ B) (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (n a))
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (hB₀ : IsFlagBundle π₀ E n fl₀) (hB : IsFlagBundle π E n fl) :
    ∃ (g' : Y ⟶ Y₀) (g'' : Y₀ ⟶ Y) (w : g' ≫ π₀ = π), g'' ≫ π = π₀ ∧ g' ≫ g'' = 𝟙 Y ∧ g'' ≫ g' = 𝟙 Y₀ ∧
      ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl₀ a).F i) ≅ (fl a).F i, e.hom ≫ (fl a).ι i =
        (Scheme.Modules.pullback g').map ((fl₀ a).ι i) ≫ (Scheme.Modules.pullbackComp g' π₀).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (E a) := by
  obtain ⟨g', ⟨w, hs⟩, -⟩ := hB₀ Y π fl
  obtain ⟨g'', ⟨w', hs'⟩, -⟩ := hB Y₀ π₀ fl₀
  refine ⟨g', g'', w, w', ?_, ?_, hs⟩
  · refine (hB Y π fl).unique ⟨by rw [Category.assoc, w', w], fun a i => ?_⟩
      ⟨Category.id_comp π, fun a i => GlobalTheory.T.pullback_id_flag_piece_iso π (E a) _ ((fl a).ι i) _⟩
    obtain ⟨e₁, he₁⟩ := hs a i
    obtain ⟨e₂, he₂⟩ := hs' a i
    exact GlobalTheory.T.flag_piece_pullback_comp_iso π π₀ π (E a) _ _ _ _ _ _ g' g'' w w' _ e₁ he₁ e₂ he₂
  · refine (hB₀ Y₀ π₀ fl₀).unique ⟨by rw [Category.assoc, w, w'], fun a i => ?_⟩
      ⟨Category.id_comp π₀, fun a i => GlobalTheory.T.pullback_id_flag_piece_iso π₀ (E a) _ ((fl₀ a).ι i) _⟩
    obtain ⟨e₁, he₁⟩ := hs' a i
    obtain ⟨e₂, he₂⟩ := hs a i
    exact GlobalTheory.T.flag_piece_pullback_comp_iso π₀ π π₀ (E a) _ _ _ _ _ _ g'' g' w' w _ e₁ he₁ e₂ he₂

end GlobalTheory.FlagTransport

namespace GlobalTheory.FlagInd

theorem flagInduces_transport : ∀ {F : Type} [Field F] [NumberField F] {C : TrueGeo.CxSt F} (Yv : ProjVar.Var F) (Bs : Scheme.{0}) (q : Bs ⟶ Sp (𝓞 F))
    (ι : Type) (E : ι → Bs.Modules) (n : ι → ℕ) (h : ∀ a, VMetric q (E a) (n a)) (H : ∀ a, (h a).IsCInf)
    (A : ∀ a, Fin (n a) → TrueGeo.Adl C Yv) (Y₀ : Scheme.{0}) (_ : IsIntegral Y₀) (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (n a)), IsFlagBundle π₀ E n fl₀ →
    ∀ (ar₀ : IsArithVar (π₀ ≫ q) Yv.dim) (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀),
    GlobalTheory.FlagInd.FlagInduces Yv q E n h H A Y₀ π₀ fl₀ ar₀ n₀ →
    ∀ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)),
      IsFlagBundle π E n fl → ∀ (arY : IsArithVar (π ≫ q) Yv.dim) (nY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y),
      GlobalTheory.FlagInd.FlagInduces Yv q E n h H A Y π fl arY nY := by
  intro F _ _ C Yv Bs q ι E n h H A Y₀ _ π₀ fl₀ hB₀ ar₀ n₀ hI Y _ π fl hB arY nY
  obtain ⟨G, _, j₀, πG, pb, _, _, φ, φs, hind⟩ := hI
  obtain ⟨g', g'', w, w', h₁, h₂, hs⟩ := GlobalTheory.FlagTransport.exists_iso π₀ π E n fl₀ fl hB₀ hB
  have pb' : IsPullback (j₀ ≫ g'') (πG ≫ Yv.str) (π ≫ q) (spMap (algebraMap (𝓞 F) F)) :=
    IsPullback.of_iso pb (Iso.refl _) ⟨g'', g', h₂, h₁⟩ (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [← w']) (by simp)
  have hf : g' ≫ π₀ ≫ q = π ≫ q := by rw [← Category.assoc, w]
  refine ⟨G, inferInstance, j₀ ≫ g'', πG, pb', inferInstance, inferInstance, φ, φs, fun a i => ?_⟩
  have t := GlobalTheory.T.normal_arith_model_generic_point_map Yv Y₀ Y (π₀ ≫ q) (π ≫ q) ar₀ n₀ arY nY g' hf G j₀ (j₀ ≫ g'')
    (by rw [Category.assoc, h₂, Category.comp_id]) πG pb pb' φ φs (A a i) _ 1 (hind a i)
  exact GlobalTheory.T.induced_metric_of_isometric _ _ _ _ 1 t (GlobalTheory.T.flag_pullback_piece_iso_factor q π₀ π (E a) (n a) (h a) (H a) (fl₀ a) (fl a) g' w
    (hs a) hf i).symm

end GlobalTheory.FlagInd

end
