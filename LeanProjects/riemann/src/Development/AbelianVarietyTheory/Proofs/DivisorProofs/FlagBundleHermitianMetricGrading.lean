import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSuccessiveQuotientLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDropStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagSuccessiveQuotientExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagQuotientConnectingMapStatement

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.SwapBundle

theorem swapFl_bundle : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp k) (d₁ : ℕ) (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) (E₁ : Y₁.Modules) (h₁ : VMetric q₁ E₁ 2)
      (H₁ : h₁.IsCInf) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (M : (Σ a, Fin (r a)) → HermLB q₁),
      D = d₁ + 1 ∧ IsArithVar q₁ d₁ ∧ IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i ((H a).pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i' ((H a).pull π w)) ∧
      ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        ((M z).pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := by
  intro k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl a i i' hi
  obtain ⟨Y₁, σ, ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v, hY₁, hproj, hsurj, hdim, hfb, hS, hs, hj,
    hSv, hPv, hEv, hPj, hSj, hx, hz⟩ := GlobalTheory.T.flag_bundle_successive_quotient_line k B Y q p d D hq hp π w ι E r (fun a => (h a).isVB) fl hfl a i i' hi
  have wρ : ρ ≫ (σ ≫ q) = p := by rw [← Category.assoc, wσ, w]
  obtain ⟨d₁, hD, had⟩ := GlobalTheory.T.arith_variety_relative_dim_drop k Y Y₁ p (σ ≫ q) ρ D wρ hp hY₁ hproj hsurj hdim
  obtain ⟨h₁, H₁, i1, i2⟩ := GlobalTheory.T.metric_flag_successive_quotient_exact k B Y Y₁ q p (σ ≫ q) π σ ρ w wσ wρ rfl (E a) (r a) (h a) (H a) (fl a) i i' hi
    S P E₁ s j t wst fl₁ hS hs hj hSv hPv hEv hPj hSj hx
  have key : ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ → ∃ M : HermLB (σ ≫ q),
      (M.pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := fun z hz' => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz z hz'.1 hz'.2
    exact GlobalTheory.T.metric_flag_quotient_connecting_map k B Y Y₁ q p (σ ≫ q) π σ ρ w wσ wρ rfl (E z.1) (r z.1) (h z.1) (H z.1) (fl z.1) z.2 (A₀ z) (A₁ z)
      (u z) (v z) h1 h2 h3 h4 h5 h6
  refine ⟨Y₁, σ ≫ q, d₁, ρ, wρ, E₁, h₁, H₁, fl₁,
    fun z => if hz' : z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ then (key z hz').choose else HermLB.triv _,
    hD, had, hfb, i1, i2, fun z h1 h2 => ?_⟩
  simp only [dif_pos (show z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ from ⟨h1, h2⟩)]
  exact (key z ⟨h1, h2⟩).choose_spec

end GlobalTheory.SwapBundle
