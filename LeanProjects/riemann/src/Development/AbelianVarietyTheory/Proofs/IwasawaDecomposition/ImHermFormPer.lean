import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusPullOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsThetaFnAndNeZeroOfIsFn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqCexpQuadraticOfEquivalentFactors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.KeyCl GlobalTheory.LocM
open Filter Topology Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilStd

open ReciprocityTheory.PTheta Matrix in

theorem im_hermForm_per {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (k k' : Fin g → ℤ) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ρ : (Fin g → ℂ) → ℂ) (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0)
    (χ : (Fin g ⊕ Fin g → ℤ) → ℂ) (hχ : ∀ r, χ r ≠ 0)
    (h : ∀ r z, ρ (z + per τ r) * (χ r * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r)))) * theta (Key.halfVec k) (Key.halfVec k') z τ =
      ρ z * theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ)
    (p q : Fin g ⊕ Fin g → ℤ) :
    (hermForm Hm (F (per τ p)) (F (per τ q))).im = omegaStd p q := by

  classical
  have hper : ∀ r : Fin g ⊕ Fin g → ℤ, per τ r =
      τ *ᵥ ofIntVec (fun i => r (Sum.inl i)) + ofIntVec (fun i => r (Sum.inr i)) := fun r => rfl
  have qp : ∀ r z, theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) z *
        theta (Key.halfVec k) (Key.halfVec k') z τ := fun r z => by
    rw [hper, ← add_assoc]
    exact thetaQuasiPeriod_holds (Fin g) _ _ z τ _ _ hτ.1
  choose c₁ hc₁ using fun r : Fin g ⊕ Fin g → ℤ =>
    NormalUnique.autFactor_eq_exp (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i))
  let lin₁ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => r (Sum.inl i)) ⬝ᵥ v)
      map_add' := fun v w => by simp only [dotProduct_add]; ring
      map_smul' := fun s v => by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring }
  let lin₂ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r))
      map_add' := fun v w => by simp only [map_add, hermForm, add_dotProduct]; ring
      map_smul' := fun s v => by simp only [map_smul, hermForm, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring }
  let c₂ : (Fin g ⊕ Fin g → ℤ) → ℂ := fun r =>
    Complex.log (χ r) + Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))
  have e1 : ∀ r v, Complex.exp (lin₁ r v + c₁ r) =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) v := fun r v => by
    rw [hc₁]; rfl
  have e2 : ∀ r v, Complex.exp (lin₂ r v + c₂ r) = χ r * Complex.exp (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) := fun r v => by
    rw [show lin₂ r v + c₂ r = Complex.log (χ r) + (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) from by
        show (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r)) + (Complex.log (χ r) +
          Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) = _
        ring, Complex.exp_add, Complex.exp_log (hχ r)]
  have hfac : ∀ r v, Complex.exp (lin₁ r v + c₁ r) * ρ v = Complex.exp (lin₂ r v + c₂ r) * ρ (v + per τ r) := by
    intro r v
    have d₁ : Differentiable ℂ fun z => Complex.exp (lin₁ r z + c₁ r) * ρ z -
        Complex.exp (lin₂ r z + c₂ r) * ρ (z + per τ r) :=
      ((((LinearMap.toContinuousLinearMap (lin₁ r)).differentiable.add_const (c₁ r)).cexp).mul hρd).sub
        ((((LinearMap.toContinuousLinearMap (lin₂ r)).differentiable.add_const (c₂ r)).cexp).mul
          (hρd.comp (differentiable_id.add_const _)))
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero _ (fun z => theta (Key.halfVec k) (Key.halfVec k') z τ) d₁
      (differentiable_theta hτ _ _) (fun z => by
        simp only [e1, e2]
        have h1 := h r z
        have h2 := qp r z
        linear_combination (-ρ z) * h2 - h1) with h0 | h0
    · exact sub_eq_zero.1 (h0 v)
    · exact absurd (funext h0) (theta_ne_zero hτ _ _)
  have key := alternating_eq_of_equivalent_factors (per τ) lin₁ lin₂ c₁ c₂ hρd.continuous hρ0 hfac p q
  set X := hermForm Hm (F (per τ p)) (F (per τ q)) with hX
  have k2 : -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ per τ q) -
      -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ per τ p) =
      (Real.pi : ℂ) * hermForm Hm (F (per τ q)) (F (per τ p)) - (Real.pi : ℂ) * X := key
  rw [hermForm_conj_symm_of_isHermitian Hm hH, ← hX, hper, hper, dotProduct_add, dotProduct_add] at k2
  have sym : ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => q (Sum.inl i)) =
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => p (Sum.inl i)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
  have sc : X - star X = 2 * (X.im : ℂ) * Complex.I := by
    have := Complex.sub_conj X
    push_cast at this
    exact this
  have om : ((omegaStd p q : ℤ) : ℂ) = ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => q (Sum.inr i)) -
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => p (Sum.inr i)) := by
    simp only [omegaStd, ofIntVec, dotProduct, ← Finset.sum_sub_distrib]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have G : (2 * Real.pi * Complex.I) * (((omegaStd p q : ℤ) : ℂ) - (X.im : ℂ)) = 0 := by
    rw [om]
    linear_combination -k2 - (2 * Real.pi * Complex.I) * sym + (Real.pi : ℂ) * sc
  rcases mul_eq_zero.1 G with h0 | h0
  · exact absurd h0 Complex.two_pi_I_ne_zero
  · exact_mod_cast (sub_eq_zero.1 h0).symm

end GlobalTheory.WeilStd

namespace GlobalTheory.WeilStd

open GlobalTheory.NormalUnique in

theorem weilIs_per : ∀ (x : KeyIn ℂ) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ),
    x.P.g = g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → c ≠ 0 →
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    u.IsFn x.th (fun z => c * thetaChar τ a b z) →
    ∀ (n : ℕ) (p q : Fin g ⊕ Fin g → ℤ) (e : ℂˣ), 0 < n →
      (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd p q : ℂ) / n) →
      Out.WeilIs x.P.A x.P.L n (u.ex ((n : ℂ)⁻¹ • per τ p)) (u.ex ((n : ℂ)⁻¹ • per τ q)) (unitOn e) := by
  intro x g u τ a b c hg hτs hτp hab hc hΛ hfn n p q e hn he
  subst hg
  obtain ⟨u₁, Hm, χ, Ef, hA, -, h1, h2, -, -, hE, -, hW⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
  obtain ⟨F, hF, hFl, -, -⟩ := HomLinear.exists_linear_of_isMonHom x.P.A x.P.A x.P.isAb x.P.isAb x.P.L x.P.L
    x.P.g x.P.g u u₁ h1 h2 (𝟙 x.P.A) inferInstance
  simp only [Category.comp_id] at hF
  obtain ⟨ρ, hρd, hρ0, -, hρ⟩ := NormalUnique.exists_frame_ratio x.P.isLB u₁ u F hF
  obtain ⟨θ₁, hθ₁⟩ := exists_isFn x.P.isLB u₁ x.th
  have hT := (isThetaFn_and_ne_zero_of_isFn x u₁ Hm χ θ₁ hA hθ₁).1
  have hrel : ∀ z, c * thetaChar τ a b z = ρ z * θ₁ (F z) := hρ x.th θ₁ _ hθ₁ hfn
  have hmem : ∀ r, F (per τ r) ∈ u₁.Λ := fun r => hFl _ ((hΛ _).2
    ⟨fun i => r (Sum.inr i), fun i => r (Sum.inl i), by simp only [per]; rw [add_comm]⟩)
  obtain ⟨k, rfl⟩ : ∃ k : Fin x.P.g → ℤ, a = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if a i = 0 then 0 else 1, funext fun i => by rcases hab.1 i with h | h <;> simp [h]⟩
  obtain ⟨k', rfl⟩ : ∃ k : Fin x.P.g → ℤ, b = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if b i = 0 then 0 else 1, funext fun i => by rcases hab.2 i with h | h <;> simp [h]⟩
  simp only [SpMove.thetaChar_half] at hrel
  have hχ : ∀ l, χ l ≠ 0 := fun l => norm_ne_zero_iff.1 (by rw [hA.2.2.1]; exact one_ne_zero)
  have key := WeilStd.im_hermForm_per (τ := τ) ⟨hτs, hτp⟩ k k' hA.1 F ρ hρd hρ0 (fun r => χ ⟨_, hmem r⟩)
    (fun r => hχ _) (fun r z => by
      have eA := hrel (z + per τ r)
      have eB := hT.2 ⟨_, hmem r⟩ (F z)
      have eC := hrel z
      rw [pow_one] at eB
      rw [map_add] at eA
      apply mul_left_cancel₀ hc
      linear_combination (ρ (z + per τ r) * (χ ⟨_, hmem r⟩ * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))))) * eC - ρ z * eA - ρ z * ρ (z + per τ r) * eB) p q
  have hEf : Ef ⟨_, hmem p⟩ ⟨_, hmem q⟩ = omegaStd p q := by
    have := hE ⟨_, hmem p⟩ ⟨_, hmem q⟩
    rw [key] at this
    exact_mod_cast this
  have hw := hW n ⟨_, hmem p⟩ ⟨_, hmem q⟩ e hn (by rw [he, hEf])
  have e1 : u.ex ((n : ℂ)⁻¹ • per τ p) = u₁.ex ((n : ℂ)⁻¹ • F (per τ p)) := by rw [← map_smul, hF]
  have e2 : u.ex ((n : ℂ)⁻¹ • per τ q) = u₁.ex ((n : ℂ)⁻¹ • F (per τ q)) := by rw [← map_smul, hF]
  rw [e1, e2]
  exact hw

end GlobalTheory.WeilStd
