import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariantsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_polAV_latticeFamily : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) := by
  intro hU hB R _ W hΔ
  obtain ⟨P, v, hg, hv, hbc, hs⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_lieBasis_invariants R W hΔ
  have hex : ∀ s : R →+* ℂ, ∃ L : PeriodPair, s W.c₄ = 12 * L.g₂ ∧ s W.c₆ = 216 * L.g₃ ∧
      s W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := fun s => by
    obtain ⟨P', φ, h⟩ := exists_isPolFibre hB s P
    obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.2.1.1 v
    obtain ⟨rig, hrig⟩ := P'.rigid
    obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := hU P' rig hrig
    obtain ⟨w, hw, -⟩ := hd v' (hv'.isTangent h.2.1 (hv.1 0))
    obtain ⟨-, L, -, hL⟩ := hs s P' φ v' u w h hv' hw
    exact ⟨L, hL⟩
  choose Lf hLf using hex
  refine ⟨P, v, Lf, ⟨hg, hv, hbc, fun s P' φ v' u w h hv' hw => ?_⟩, hLf⟩
  obtain ⟨hw0, L, hL, h4, h6, -⟩ := hs s P' φ v' u w h hv' hw
  have e : (Lf s).lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq
      (mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ((hLf s).1.symm.trans h4))
      (mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ((hLf s).2.1.symm.trans h6))
  exact ⟨hw0, fun z => e ▸ hL z⟩

end GlobalTheory
