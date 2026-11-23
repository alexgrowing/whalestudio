import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion.Conj

open PeriodPair

theorem ptHom_eq_iff_of_eq {W : WeierstrassCurve ℂ} {ρ ρ' : ℂ →+* ℂ} (e : ρ = ρ') {P Q : Fin 3 → ℂ}
    (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P)
    (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ') Q) :
    GlobalTheory.WeierstrassCurve.ptHom W ρ P hP = GlobalTheory.WeierstrassCurve.ptHom W ρ' Q hQ ↔
      ∃ v : ℂˣ, Q = (v : ℂ) • P := by
  subst e
  exact GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff W hP hQ

theorem rel_iff (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ) (hΩ₀ : Ω₀ ≠ 0) (hΩ₁ : Ω₁ ≠ 0)
    (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (z z' : ℂ) :
    (pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ↔
      GlobalTheory.ConjPoint.IsConj (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀) (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁) g
        (Ω₀ * z) (Ω₁ * z') := by
  have H₀ := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have H₁ := GlobalTheory.isHomothetic_scalePeriods Λ₁ Ω₁ hΩ₁
  unfold pt
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, spMap, GlobalTheory.WeierstrassCurve.SpecMap_ptHom,
    ptHom_eq_iff_of_eq ((RingHom.id_comp _).trans (RingHom.comp_id _).symm)]
  unfold GlobalTheory.ConjPoint.IsConj
  rw [H₀ z, H₁ z', H₀.weierstrassP_mul, H₁.weierstrassP_mul, H₀.derivWeierstrassP_mul,
    H₁.derivWeierstrassP_mul]
  by_cases hz : z ∈ Λ₀.lattice <;> by_cases hz' : z' ∈ Λ₁.lattice
  · simp only [coords, hz, hz', if_true]
    refine iff_of_true ⟨1, ?_⟩ (Or.inl ⟨trivial, trivial⟩)
    ext i; fin_cases i <;> simp
  · simp only [coords, hz, hz', if_true, if_false]
    refine iff_of_false ?_ (by tauto)
    rintro ⟨v, hv⟩
    have := congrFun hv 2
    simp at this
    exact v.ne_zero this.symm
  · simp only [coords, hz, hz', if_true, if_false]
    refine iff_of_false ?_ (by tauto)
    rintro ⟨v, hv⟩
    have := congrFun hv 2
    simp at this
  · simp only [coords, hz, hz', if_false, not_false_iff, true_and, false_and, false_or]
    constructor
    · rintro ⟨v, hv⟩
      have h2 := congrFun hv 2
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      have g2 : g 2 = 2 := map_ofNat g 2
      simp [g2] at h0 h1 h2
      rw [← h2] at h0 h1
      simp only [map_mul, map_inv₀, map_pow]
      constructor
      · linear_combination -h0
      · linear_combination -2 * h1
    · rintro ⟨e1, e2⟩
      simp only [map_mul, map_inv₀, map_pow] at e1 e2
      refine ⟨1, ?_⟩
      funext i
      have g2 : g 2 = 2 := map_ofNat g 2
      fin_cases i <;> simp [g2] <;> first | linear_combination -e1 | linear_combination (-1/2 : ℂ) * e2

theorem pt_conj_onto_add : ∀ (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 → ∀ h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁, (∀ z', ∃ z, pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ∧ ∀ z w z' w', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z → pt Λ₁ Ω₁ w' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ w → pt Λ₁ Ω₁ (z' + w') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (z + w) := by
  intro Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ h
  have H₀ := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have H₁ := GlobalTheory.isHomothetic_scalePeriods Λ₁ Ω₁ hΩ₁
  have g4 : g 4 = 4 := map_ofNat g 4
  have e₄ := congrArg WeierstrassCurve.a₄ h
  have e₆ := congrArg WeierstrassCurve.a₆ h
  simp [curve, g4] at e₄ e₆
  have h₂ : (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁).g₂ = g (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀).g₂ := by
    rw [H₁.g₂_eq, H₀.g₂_eq, map_mul, map_inv₀, map_pow]
    linear_combination -e₄
  have h₃ : (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁).g₃ = g (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀).g₃ := by
    rw [H₁.g₃_eq, H₀.g₃_eq, map_mul, map_inv₀, map_pow]
    linear_combination -e₆
  obtain ⟨s, -, hs⟩ := GlobalTheory.ConjPoint.exists_conjEquiv h₂ h₃
  have R := rel_iff Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ h
  refine ⟨fun z' => ?_, fun z w z' w' hz hw => ?_⟩
  · obtain ⟨t, ht⟩ := GlobalTheory.latticePoint_surjective _ (s.symm (GlobalTheory.latticePoint _ (Ω₁ * z')))
    refine ⟨Ω₀⁻¹ * t, (R _ _).2 ((hs _ _).2 ?_)⟩
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hΩ₀, _root_.one_mul, ht, AddEquiv.apply_symm_apply]
  · rw [R, hs] at hz hw ⊢
    rw [_root_.mul_add, _root_.mul_add, GlobalTheory.latticePoint_add, GlobalTheory.latticePoint_add, map_add, hz, hw]

end GlobalTheory.CMTorsion.Conj
