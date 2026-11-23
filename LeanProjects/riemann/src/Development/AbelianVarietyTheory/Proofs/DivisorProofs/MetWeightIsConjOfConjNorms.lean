import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPointNormPowEq

namespace MetricConjugation
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MetConj

theorem pn_eq_of_generatesAt {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}
    {f : Y.Fn} {y : Pts Y σ} (hf : Δ.GeneratesAt (under y) f) (m : C.Met Y σ Δ) :
    C.pn Y σ Δ m (C.cx Y σ f) y =
      ‖ratVal (f * (eqn Δ (under y) : Y.Fn)) y‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ (genAt Δ (under y))) y := by
  have he := Base.isEqn_eqn Δ (under y)
  have hu := he.generatesAt_iff.1 hf
  rw [← C.pn_mul Y σ Δ m _ _ y hu.regAt (generatesAt_genAt Δ _).regularAt]
  congr 2
  simp [genAt]

theorem metWeight_isConj : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y), (∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → C.pn Y σ' Δ (m σ') (C.cx Y σ' (genAt Δ (under y'))) y' = C.pn Y σ Δ (m σ) (C.cx Y σ (genAt Δ (under y))) y) → ∀ σ σ', (metWeight Δ (m σ) (hm σ)).IsConj (metWeight Δ (m σ') (hm σ')) := by
  intro F _ _ C Y Δ m hm hc σ σ' i y y' hy hi
  have hu : under y' = under y := by
    show below y'.1 = below y.1
    rw [hy]
    exact HtIndep.below_spMap_comp _ _
  have hi' : under y ∈ i.1.1 := mem_ptsIn.1 hi
  have hg : Δ.GeneratesAt (under y) ((i.1.2 : Y.Fn))⁻¹ := CartierDiv.isEqn_iff_generatesAt_inv.1 (i.2.2 _ hi')
  have hg' : Δ.GeneratesAt (under y') ((i.1.2 : Y.Fn))⁻¹ := hu ▸ hg
  rw [metWeight_φ, metWeight_φ, pn_eq_of_generatesAt hg (m σ), pn_eq_of_generatesAt hg' (m σ'), hc σ σ' y y' hy, hu,
    norm_ratVal_of_conj hy]

end GlobalTheory.CompanionTheory.MetConj

end
end

end MetricConjugation
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.metWeight_isConj_of_conj_norms : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y), (∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → C.pn Y σ' Δ (m σ') (C.cx Y σ' (genAt Δ (under y'))) y' = C.pn Y σ Δ (m σ) (C.cx Y σ (genAt Δ (under y))) y) → ∀ σ σ', (metWeight Δ (m σ) (hm σ)).IsConj (metWeight Δ (m σ') (hm σ')) := by
  first | exact @MetricConjugation.GlobalTheory.CompanionTheory.MetConj.metWeight_isConj | exact MetricConjugation.GlobalTheory.CompanionTheory.MetConj.metWeight_isConj | (intros; apply MetricConjugation.GlobalTheory.CompanionTheory.MetConj.metWeight_isConj <;> assumption)

end
