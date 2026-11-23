import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformisationTangentUnimodularRiemanStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPrincipalDimOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem isLieNormSq_iff_eq_pi_div_covolume :
    ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (L : PeriodPair), P.g = 1 → IsTangent v → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → 0 < Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ ∀ r, IsLieNormSq P v s r ↔ r = Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  intro hU hB R _ P v s L hg hv hΛ
  have key : ∀ r, IsLieNormSq P v s r → 0 < r ∧ r = Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
    rintro r ⟨P', φ, v', u, Hm, χ, w, hP, hv', hA, hd, rfl⟩
    obtain ⟨hw, hL⟩ := hΛ P' φ v' u w hP hv' hd
    obtain ⟨Ef, hEf, hbij⟩ := (GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).2.2 Hm χ hA
    have hpos : 0 < (hermForm Hm w w).re := hA.2.1 w hw
    have e := hermForm_principal_dim_one P'.g u.Λ w L Hm Ef (hP.1.trans hg) hw hL hA.1 hpos hEf hbij 1 1
    refine ⟨mul_pos Real.pi_pos hpos, ?_⟩
    rw [one_smul, map_one, _root_.mul_one, one_div, ← Complex.ofReal_inv] at e
    rw [e, Complex.ofReal_re, div_eq_mul_inv]
  obtain ⟨r₀, h₀⟩ := exists_isLieNormSq hU hB P hv s
  obtain ⟨h1, h2⟩ := key r₀ h₀
  exact ⟨h2 ▸ h1, fun r => ⟨fun h => (key r h).2, fun h => (h.trans h2.symm) ▸ h₀⟩⟩

end GlobalTheory
