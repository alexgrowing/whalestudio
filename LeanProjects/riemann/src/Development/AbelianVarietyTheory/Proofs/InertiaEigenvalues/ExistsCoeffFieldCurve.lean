import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FixesRootOfActsTorsion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesCurveMulCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.DeepCoeff

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber GlobalTheory.FieldSize GlobalTheory.WeberFixed

def preimageField (τ : ℂ ≃+* ℂ) (K : IntermediateField ℚ ℂ) : IntermediateField ℚ ℂ :=
  K.comap ((τ : ℂ →+* ℂ).toRatAlgHom)

theorem exists_coeff_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l l₂ : Level H) (c : Coeff l) (n p : ℕ), p.Prime → ¬ p ∣ n → Nat.Coprime l.M n → l₂.M = l.M * n → l₂.A = 1 → l.GoodAt p → CurveOver H c.F l.M → ∃ c' : Coeff l₂, c.F ≤ c'.F ∧ CurveOver H c'.F l₂.M ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c'.F, τ x ∈ c'.F) ∧ ∀ A : ValuationSubring ℂ, (p : ℂ) ∈ A.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → ∀ x ∈ c'.F, τ x = x := by
  intro E _ _ _ H l l₂ c n p hp hpn hco hM hA hgood hcurve
  obtain ⟨L, hL⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H
  have h3 := l₂.three_le
  have hN : 0 < l₂.M := by omega
  have hN0 : (l₂.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨hfin, halg, hperm⟩ := weberSet_finite_algebraic_permuted L l₂.M hN (g₂_ne_zero H L hL) (g₃_ne_zero H L hL)
  have hζ : IsPrimitiveRoot (zeta l₂.M) l₂.M := Complex.isPrimitiveRoot_exp _ hN.ne'
  let S : Set ℂ := insert (zeta l₂.M) (weberSet L l₂.M)
  have := (hfin.insert (zeta l₂.M)).to_subtype
  have hS : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro x (rfl | hx)
    · exact (hζ.isIntegral hN).tower_top
    · exact (halg (GlobalTheory.WeberField.invariant_isAlgebraic H L hL) x hx).isIntegral
  have := c.fin
  let F := c.F ⊔ IntermediateField.adjoin ℚ S
  have hl : c.F ≤ F := le_sup_left
  have hr : ∀ x ∈ S, x ∈ F := fun x hx => le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ S hx)
  have hrt : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hle : ∀ K : IntermediateField ℚ ℂ, c.F ≤ K → S ⊆ K → F ≤ K := fun K h₁ h₂ =>
    sup_le h₁ (IntermediateField.adjoin_le_iff.2 h₂)
  refine ⟨⟨F, inferInstance, fun τ a => hl (c.conj τ a), ?_, ?_⟩, hl, fun τ hτ => ?_, fun τ hτ => ⟨?_, ?_⟩⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
    exact hr _ (.inl rfl)
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact hl hrt
    · rw [hA, show zeta 1 = 1 by simp [zeta]]
      exact one_mem F
  · exact fixesCurve_of_weber E H L _ hN hL τ (hτ _ (hl hrt)) (hτ _ (hr _ (.inr (.inl rfl))))
      fun s hs => hτ _ (hr _ (.inr (.inr ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)))
  · have hj := weber_fixed H L hL (hcurve τ hτ) _ (.inl rfl)
    refine hle (preimageField τ F) (fun x hx => ?_) ?_
    · show τ x ∈ F
      rw [hτ x hx]
      exact hl hx
    rintro x (rfl | rfl | ⟨z, hz, hz', rfl⟩)
    · show τ (zeta l₂.M) ∈ F
      have : NeZero l₂.M := ⟨hN.ne'⟩
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (zeta l₂.M)) (by rw [← map_pow, hζ.pow_eq_one, map_one])
      rw [← hk]
      exact pow_mem (hr _ (.inl rfl)) _
    · show τ _ ∈ F
      rw [hj]
      exact hr _ (.inr (.inl rfl))
    · show τ _ ∈ F
      obtain ⟨t, h₁, h₂, h₃⟩ := hperm τ hj (z / l₂.M) (by rwa [mul_div_cancel₀ _ hN0]) hz'
      rw [h₃]
      have e : l₂.M * t / l₂.M = t := mul_div_cancel_left₀ _ hN0
      exact hr _ (.inr (.inr ⟨_, h₁, by rwa [e], by rw [e]⟩))
  · intro A hpA hin
    have hfix : FixesCurve H τ l₂.M := hM ▸ GlobalTheory.T.fixesCurve_mul_coprime E H l.M n p A τ hp hpA hpn hco hgood (hcurve τ hτ) hin
    let K : IntermediateField ℚ ℂ :=
      ((τ : ℂ →+* ℂ).eqLocusField (RingHom.id ℂ)).toIntermediateField fun q => by
        show τ (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q
        simp
    refine hle K hτ ?_
    rintro x (rfl | hx)
    · exact zeta_fixed H (by omega) hfix
    · exact weber_fixed H L hL hfix x hx

end GlobalTheory.DeepCoeff
