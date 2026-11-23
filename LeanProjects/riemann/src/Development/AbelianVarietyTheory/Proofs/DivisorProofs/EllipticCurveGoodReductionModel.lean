import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JInvariantIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveAbelianSchemeModelStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMPlaceCurve

theorem sz_of_pow {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {y : ℂ} {n : ℕ} (hn : 0 < n)
    (h : Sz l lam 0 (y ^ n)) : Sz l lam 0 y := by
  obtain ⟨hy, hn'⟩ := h
  have ha : IsAlgebraic ℚ y := IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 hy)
  have hy' : y ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.2 ha
  refine ⟨hy', ?_⟩
  rw [Real.rpow_zero] at hn' ⊢
  have e : (⟨y ^ n, hy⟩ : algebraicClosure ℚ ℂ) = (⟨y, hy'⟩ : algebraicClosure ℚ ℂ) ^ n := rfl
  rw [e, map_pow, norm_pow] at hn'
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 hn'

theorem exists_curve : GlobalTheory.Published.SerreTateGoodReductionSt →
  ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ), FiniteDimensional ℚ k₁ ∧ IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧
        u.IsDiff (fun _ ↦ t) v' ∧ t ≠ 0 ∧ Sz l lam 0 ((t * Ω)⁻¹) := by
  intro _ d Λ hd hΛ l _ lam Ω hΩ
  have hJ := GlobalTheory.T.j_invariant_integral d Λ hd hΛ
  obtain ⟨k₁, R₁, W, hk, hpl, hsub, hΔ, hj⟩ := GlobalTheory.T.weierstrass_model_good_reduction l lam _ hJ
  have hD : latDisc Λ ≠ 0 := g₂_cube_sub_g₃_sq_ne_zero Λ
  have hΔ0 : ((W.Δ : R₁) : ℂ) ≠ 0 := by
    intro h0
    exact hΔ.ne_zero (Subtype.ext h0)
  have hrel : 1728 * ((W.Δ : R₁) : ℂ) = ((W.c₄ : R₁) : ℂ) ^ 3 - ((W.c₆ : R₁) : ℂ) ^ 2 := by
    have := congrArg (fun x : R₁ ↦ (x : ℂ)) W.c_relation
    push_cast at this
    exact this
  have hΔ' : (((W.c₄ : R₁) : ℂ) / 12) ^ 3 - 27 * (((W.c₆ : R₁) : ℂ) / 216) ^ 2 = ((W.Δ : R₁) : ℂ) := by
    linear_combination -hrel / 1728
  have e : Λ.g₂ ^ 3 * ((((W.c₄ : R₁) : ℂ) / 12) ^ 3 - 27 * (((W.c₆ : R₁) : ℂ) / 216) ^ 2) =
      (((W.c₄ : R₁) : ℂ) / 12) ^ 3 * (Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2) := by
    rw [hΔ', div_pow, hj]
    unfold latDisc at hD ⊢
    field_simp
    ring
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq hD (by rw [hΔ']; exact hΔ0) e
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hu (by simpa using hc.symm)
  have h4 : ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; linear_combination 12 * h2
  have h6 : ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ := by
    rw [show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; linear_combination 216 * h3
  obtain ⟨P, A', _, φ', L', uu, v, v', h1, h2', h3', h4', h5, h6', h7, h8⟩ := GlobalTheory.T.elliptic_curve_abelian_scheme_model R₁ W hΔ Λ c hc0 h4 h6
  have hΩ0 : Ω ≠ 0 := by rintro rfl; apply hD; rw [← hΩ]; norm_num
  have key : (c * Ω) ^ 12 = ((W.Δ : R₁) : ℂ) := by
    rw [← hΔ', h4, h6, mul_pow, hΩ]
    unfold latDisc
    ring
  refine ⟨k₁, R₁, hk, hpl, hsub, P, A', inferInstance, φ', L', uu, v, v', c, h1, h2', h3', h4', h5, h6', h7, h8, hc0, ?_⟩
  obtain ⟨w, hw⟩ := hΔ
  refine sz_of_pow (n := 12) (by norm_num) ?_
  have e2 : ((c * Ω)⁻¹) ^ 12 = ((w⁻¹ : R₁ˣ) : R₁) := by
    rw [inv_pow, key, ← hw]
    have := congrArg (fun x : R₁ ↦ (x : ℂ)) w.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at this ⊢
    exact (eq_inv_of_mul_eq_one_right this).symm
  rw [e2]
  exact hpl.2.1 _ (w⁻¹ : R₁ˣ).1.2

end GlobalTheory.CMPlaceCurve
