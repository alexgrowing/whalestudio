import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer.Hol

def jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W) (v : E) :
    Hol W →ₐ[ℂ] DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h))
  map_one' := by
    ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by
    ext <;> simp
  map_add' f g := by
    ext <;> simp <;> ring
  commutes' c := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem jet_spec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W)
    (v : E) (h : Hol W) : (jet hp v h).fst = h.fn p ∧ (jet hp v h).snd = fderiv ℂ h.fn p v := by
  constructor
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).fst = _
    simp [ev_apply]
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).snd = _
    simp [ev_apply, fn_der v h hp]

end GlobalTheory.AnPer.Hol

theorem GlobalTheory.AnPer.Hol.exists_jet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  intro E _ _ W p hp v
  exact ⟨GlobalTheory.AnPer.Hol.jet hp v, GlobalTheory.AnPer.Hol.jet_spec hp v⟩
