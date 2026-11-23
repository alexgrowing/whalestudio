import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

open scoped UpperHalfPlane

namespace GlobalTheory.CMModel

theorem j_mul_Δ_eq (F : Type) [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', mul_comm]
  exact _root_.Units.mul_inv_cancel_left W.Δ' _

theorem exists_upper_of_sq_eq_neg {d : ℕ} {τ : ℂ} (hd : 0 < d) (h : τ ^ 2 = -(d : ℂ)) :
    ∃ τ₀ : ℍ, (τ₀ : ℂ) = τ ∨ (τ₀ : ℂ) = -τ := by
  have him : τ.im ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h
    simp [pow_two, h0] at h1
    have : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg τ.re]
  rcases lt_or_gt_of_ne him with hn | hp
  · exact ⟨⟨-τ, by simpa using hn⟩, Or.inr rfl⟩
  · exact ⟨⟨τ, hp⟩, Or.inl rfl⟩

theorem modularJ_mem_Qb {d : ℕ} {τ₀ : ℍ} (h : (τ₀ : ℂ) ^ 2 = -(d : ℂ)) :
    modularJ τ₀ ∈ algebraicClosure ℚ ℂ := by
  have hi : _root_.IsIntegral ℤ (modularJ τ₀) :=
    isIntegral_modularJ_of_quadratic (a := 1) (b := 0) (c := d) one_ne_zero (by push_cast; rw [h]; ring)
  exact mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic

end GlobalTheory.CMModel

theorem GlobalTheory.CMModel.exists_curve_lattice :
    ∀ (d : ℕ) (τ : ℂ), 0 < d → τ ^ 2 = -(d : ℂ) →
  ∃ (A₀ : Over (Sp Qb)) (_ : GrpObj A₀) (A : Over (Sp ℂ)) (_ : GrpObj A) (p : A.left ⟶ A₀.left) (L : LB A.left)
    (u : HolUnif A L 1) (c : ℂ), IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A₀.hom ∧
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p ∧ L.IsLB ∧ c ≠ 0 ∧ ∀ z ∈ u.Λ, ∃ a b : ℤ, z 0 = c * (a + b * τ) := by
  classical
  intro d τ hd hτ
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.CMModel.exists_upper_of_sq_eq_neg hd hτ
  have hτ₀2 : (τ₀ : ℂ) ^ 2 = -(d : ℂ) := by rcases hτ₀ with e | e <;> rw [e] <;> simp [hτ]
  let j : Qb := ⟨GlobalTheory.modularJ τ₀, GlobalTheory.CMModel.modularJ_mem_Qb hτ₀2⟩
  let W : WeierstrassCurve Qb := WeierstrassCurve.ofJ j
  have hWj : W.j = j := WeierstrassCurve.ofJ_j j
  have hΔ : IsUnit W.Δ := (inferInstance : W.IsElliptic).isUnit
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hU'⟩, hLf⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds Qb W hΔ
  let s : Qb →+* ℂ := algebraMap Qb ℂ
  obtain ⟨P', φ, h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds s P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, -, -, -, -, -, hd', -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd' v' (hv'.isTangent h.2.1 (hv.1 0))
  obtain ⟨hw0, hmem⟩ := hU' s P' φ v' u w h hv' hw
  have hj : s W.j = (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀)).j := by
    rw [hWj, GlobalTheory.latticeCurve_j one_ne_zero (GlobalTheory.mem_lattice_periodPairOfTau τ₀)]
    rfl
  have e1 := congrArg s (GlobalTheory.CMModel.j_mul_Δ_eq Qb W)
  rw [map_mul, map_pow, hj, (hLf s).1, (hLf s).2.2] at e1
  have e2 := GlobalTheory.CMModel.j_mul_Δ_eq ℂ (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀))
  rw [GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄] at e2
  have key : (GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 * ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) =
      (Lf s).g₂ ^ 3 * ((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) := by
    linear_combination (((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) * e1 -
      ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) * e2) / 1728
  obtain ⟨c, hc0, hc⟩ := (GlobalTheory.lattice_determined_by_invariants (GlobalTheory.periodPairOfTau τ₀) (Lf s)).2 key
  cases P' with | mk A' isAb' g' sm' L' isLB' rig' sym' amp' kt' => ?_
  have e : g' = 1 := h.1.trans hg
  subst e
  have hw00 : w 0 ≠ 0 := fun h0 => hw0 (funext fun i => by fin_cases i; exact h0)
  refine ⟨P.A, inferInstance, A', inferInstance, φ, L', u, w 0 * c, P.isAb, hg ▸ P.smoothDim, h.2.1,
    isLB', mul_ne_zero hw00 hc0, fun z hz => ?_⟩
  have hz' : z = (z 0 / w 0) • w := funext fun i => by
    fin_cases i
    simp [hw00]
  obtain ⟨x, hx, hxz⟩ := (hc _).1 ((hmem (z 0 / w 0)).2 (hz' ▸ hz))
  obtain ⟨m, n, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ₀ x).1 hx
  have hz0 : z 0 = w 0 * c * (1 * (m * (τ₀ : ℂ) + n)) := by
    rw [_root_.mul_assoc, ← hxz]
    field_simp
  rcases hτ₀ with e | e
  · exact ⟨n, m, by rw [hz0, e]; ring⟩
  · exact ⟨n, -m, by rw [hz0, e]; push_cast; ring⟩
