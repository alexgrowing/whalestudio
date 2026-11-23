import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagSuccessiveQuotientExact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_flag_successive_quotient_exact : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (i i' : Fin n), (i' : ℕ) = i + 1 → ∀ (S P E₁ : Y₁.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback σ).obj E)
    (t : P ⟶ E₁) (wst : s ≫ t = 0) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    (ShortComplex.mk s t wst).ShortExact → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j → GlobalTheory.VB.IsVB S i →
    GlobalTheory.VB.IsVB P ((i : ℕ) + 2) → GlobalTheory.VB.IsVB E₁ 2 →
    (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ fl.F i'.succ, e.hom ≫ fl.ι i'.succ =
      (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ fl.F i.castSucc, e.hom ≫ fl.ι i.castSucc =
      (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ (x : fl.F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : fl.F i.succ ⟶ fl₁.F 1),
      x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E = fl.ι i.succ ∧
      g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) →
    ∃ (h₁ : VMetric q₁ E₁ 2) (H₁ : h₁.IsCInf),
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i (H.pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i' (H.pull π w)) := by
  first | exact @GlobalTheory.SubqPair.exists_isometric_pair | exact GlobalTheory.SubqPair.exists_isometric_pair | (intros; apply GlobalTheory.SubqPair.exists_isometric_pair <;> assumption)
