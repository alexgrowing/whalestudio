import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZeroStatement
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.CxForm (IsRegVar HolAtlas)
open GlobalTheory

namespace GlobalTheory.ExactIntegral

theorem integral_eq_of_isExact {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : HolAtlas M n) (α β : A.Fld) (hα : A.IsForm α)
    (h : A.IsExact (α - β)) : A.integral α = A.integral β := by
  obtain ⟨u, w, hu, hw, e⟩ := h
  have alg := (HolAtlas.isForm_algebra M n A).2
  have hdu : A.IsForm (A.del u) := (A.isForm_del_dbar hu).1
  have hdw : A.IsForm (A.dbar w) := (A.isForm_del_dbar hw).2
  have h1 : A.IsForm (α - A.del u) := by
    have := (alg 0 _ _ hα (alg (-1) _ _ hdu hdu).2.2).1
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have eβ : β = α - A.del u - A.dbar w := by
    rw [sub_sub, ← e, sub_sub_cancel]
  rw [eβ, HolAtlas.integral_sub_of_isForm A _ _ h1 hdw, HolAtlas.integral_sub_of_isForm A _ _ hα hdu,
    (GlobalTheory.T.integral_del_dbar_zero M n A u hu).1, (GlobalTheory.T.integral_del_dbar_zero M n A w hw).2, sub_zero, sub_zero]

theorem integral_eq_of_isExact_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1)
    (σ : k →+* ℂ) (α β : (h.atlas σ).Fld), (h.atlas σ).IsRealForm 1 α → (h.atlas σ).IsExact (α - β) →
    (h.atlas σ).integral α = (h.atlas σ).integral β := by
  intro k _ X p h σ α β hα hex
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ h.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  exact integral_eq_of_isExact (h.atlas σ) α β hα.1 hex

end GlobalTheory.ExactIntegral
