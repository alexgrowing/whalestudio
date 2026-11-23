import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtEqOfResidueFieldHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMulFderivOfTsupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumSubConst

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.TrivNef

theorem ratVal_eq_valAt {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (f : Z.functionField) (y : CxPts q σ) : ratVal f y = valAt y.1 f := by
  by_cases h : RegAt (under y) f
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    have hy : y ∈ CxPts.ptsIn q σ U := CxPts.mem_ptsIn.2 hU
    rw [ratVal_fnOf hy, OfModel.valAt_fnOf y.1 hU hy, CxPts.ev_eq hy]
    rfl
  · rw [ratVal, dif_neg h, valAt, dif_neg h]

theorem finsum_neg_log {α K : Type} [Field K] (w : K →* ℝ) (hw : ∀ a, a ≠ 0 → w a ≠ 0) {p : α → Prop}
    (hp : {y | p y}.Finite) (f : α → K) (hf : ∀ y, p y → f y ≠ 0) :
    ∑ᶠ (y : α) (_ : p y), -Real.log (w (f y)) = -Real.log (w (∏ᶠ (y : α) (_ : p y), f y)) := by
  have h₁ := finsum_mem_eq_finite_toFinset_sum (fun y => -Real.log (w (f y))) hp
  have h₂ := finprod_mem_eq_finite_toFinset_prod f hp
  refine h₁.trans (Eq.trans ?_ (congrArg (fun a => -Real.log (w a)) h₂).symm)
  rw [map_prod, Real.log_prod fun y hy => hw _ (hf y (hp.mem_toFinset.1 hy)), Finset.sum_neg_distrib]

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.TrueGeo.TrivNef
