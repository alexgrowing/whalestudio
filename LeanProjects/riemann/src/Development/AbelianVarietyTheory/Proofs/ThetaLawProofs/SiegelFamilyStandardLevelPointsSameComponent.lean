import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPeriodLevelOfSiegelPointStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointOfPerLev
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponentStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelConnected

theorem convex_siegel (h : ℕ) :
    Convex ℝ {τ : Matrix (Fin h) (Fin h) ℂ | τ.IsSymm ∧ (τ.map Complex.im).PosDef} := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ a b ha hb hab
  refine ⟨(hx.smul a).add (hy.smul b), ?_⟩
  have e : (a • x + b • y).map Complex.im = a • x.map Complex.im + b • y.map Complex.im := by
    ext i j
    simp
  rw [e]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by simpa using hab
    subst this
    simpa using hy'
  · exact (hx'.smul ha').add_posSemidef (hy'.posSemidef.smul hb)

variable {o : Type} [CommRing o] {S : Scheme.{0}} {s : S ⟶ Sp o} {σ : o →+* ℂ}

theorem sameComp_symm {p q : Sp ℂ ⟶ S} (h : SameComp s σ p q) : SameComp s σ q p := by
  obtain ⟨hp, hq, H⟩ := h
  refine ⟨hq, hp, fun z => ?_⟩
  rw [← connectedComponent_eq (H z)]
  exact mem_connectedComponent

theorem sameComp_trans {p q r : Sp ℂ ⟶ S} (h : SameComp s σ p q) (h' : SameComp s σ q r) :
    SameComp s σ p r := by
  obtain ⟨hp, hq, H⟩ := h
  obtain ⟨hq', hr, H'⟩ := h'
  refine ⟨hp, hr, fun z => ?_⟩
  rw [connectedComponent_eq (H' z)]
  exact H z

theorem mem_siegel_of_ptAt {h k : ℕ} {ζ : o} {c : SiegPre h k ζ s} {p : Sp ℂ ⟶ S}
    {τ : Matrix (Fin h) (Fin h) ℂ} (H : PtAt c p τ) : τ.IsSymm ∧ (τ.map Complex.im).PosDef := by
  obtain ⟨P, lev, φ, hP, -⟩ := H
  exact ⟨hP.2.1, hP.2.2.1⟩

theorem sameComp_of_ptAt : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ' → SameComp F.s σ p q := by
  intro hL hL2 hT hA h k K _ ζ σ F hh hk hodd hζ τ τ' p q hp hq hpτ hqτ
  have hopen := GlobalTheory.T.siegelFamily_nearbyPeriods_same_component hL hL2 hT h k K ζ σ F hh hk hodd hζ
  have hex : ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm ∧ (t.map Complex.im).PosDef →
      ∃ r : Sp ℂ ⟶ F.X, r ≫ F.s = spMap σ ∧ PtAt F.univ r t := by
    rintro t ⟨ht, ht'⟩
    obtain ⟨P, lev, hP⟩ := GlobalTheory.T.exists_periodLevel_of_siegel_point hT hA h k t ht ht'
    obtain ⟨r, φ, hr, hsq, hlev⟩ := GlobalTheory.KeyFam.exists_point_of_perLev hL h k K ζ σ F hh hk hodd hζ P t lev hP
    exact ⟨r, hr, P, lev, φ, hP, hsq, hlev⟩
  have key := (convex_siegel h).isPreconnected.induction₂'
    (fun t t' => ∀ r : Sp ℂ ⟶ F.X, r ≫ F.s = spMap σ → PtAt F.univ r t →
      ∃ r' : Sp ℂ ⟶ F.X, r' ≫ F.s = spMap σ ∧ PtAt F.univ r' t' ∧ SameComp F.s σ r r')
    (by
      intro x hx
      obtain ⟨r₀, hr₀, hr₀x⟩ := hex x hx
      obtain ⟨N, hN, HN⟩ := hopen x r₀ hr₀ hr₀x
      filter_upwards [mem_nhdsWithin_of_mem_nhds hN, self_mem_nhdsWithin] with y hyN hy
      refine ⟨fun r hr hrx => ?_, fun r hr hry => ⟨r₀, hr₀, hr₀x, HN y hyN r hr hry⟩⟩
      obtain ⟨r', hr', hr'y⟩ := hex y hy
      exact ⟨r', hr', hr'y, sameComp_trans (HN x (mem_of_mem_nhds hN) r hr hrx)
        (sameComp_symm (HN y hyN r' hr' hr'y))⟩)
    (by
      intro x y z _ _ _ hxy hyz r hr hrx
      obtain ⟨r', hr', hr'y, h₁⟩ := hxy r hr hrx
      obtain ⟨r'', hr'', hr''z, h₂⟩ := hyz r' hr' hr'y
      exact ⟨r'', hr'', hr''z, sameComp_trans h₁ h₂⟩)
    (mem_siegel_of_ptAt hpτ) (mem_siegel_of_ptAt hqτ)
  obtain ⟨q', hq', hq'τ, h₁⟩ := key p hp hpτ
  obtain ⟨N, hN, HN⟩ := hopen τ' q hq hqτ
  exact sameComp_trans h₁ (HN τ' (mem_of_mem_nhds hN) q' hq' hq'τ)

end GlobalTheory.SiegelConnected
