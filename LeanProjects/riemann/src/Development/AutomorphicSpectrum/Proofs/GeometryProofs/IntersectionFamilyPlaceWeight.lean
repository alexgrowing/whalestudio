import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatTwistStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstantStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariantStatement

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem constLine_zero_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    (constLine (ι := ι) 0).tensor (constLine 0) = constLine 0 := by
  simp [HermLine.tensor, constLine, HermLine.ofWeight]

theorem ptsIntegral_eq_mean : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ I W n L d t u hI hd hO hle hW hL ht hu
  have hex := fun σ : F →+* ℂ => GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (Set.indicator {σ} 1) hO
  choose χ hχ _ using hex
  have hsplit : ∀ (t' : (F →+* ℂ) → ℝ) (u' : ((Σ k, ι k) → ℂ) → ℝ),
      (∀ σ z, PtOver y φ σ z → u' z = t' σ) →
      ptsIntegral W (pot L) u' = ∑ σ : F →+* ℂ, t' σ * ptsIntegral W (pot L) (χ σ) :=
    fun t' u' h => GlobalTheory.T.green_current_integral_formula hPI K ι Ω F y φ W n L t' u' χ hO hle hW hL h hχ
  have hc : IsSmoothHerm (constLine (ι := ι) 0) := contDiffOn_const
  have hzero : I W (n + 1) (Fin.snoc L (constLine 0)) = 0 := by
    have h := hI.2.1 W n L (constLine 0) (constLine 0) hW hL hc hc
    rw [constLine_zero_tensor] at h
    linarith
  have hunit : ∀ α : (𝓞 F)ˣ,
      ∑ σ : F →+* ℂ, Real.log ‖σ ((α : 𝓞 F) : F)‖ * ptsIntegral W (pot L) (χ σ) = 0 := by
    intro α
    obtain ⟨S, -, hκ⟩ := GlobalTheory.T.flat_herm_unit_constant K ι Ω F y φ α hO
    obtain ⟨v, hv, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
    have h1 := GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L (constLine 0) S d v hI hd hO hle hW hL hc hv
    have h2 := hsplit (fun σ => Real.log (S.κ σ)) v fun σ z hz => (hv.near σ z hz).self_of_nhds
    simp only [hκ] at h2
    linarith
  have hmain := sum_eq_mean_of_units F (fun σ => ptsIntegral W (pot L) (χ σ)) t hunit ht
  have hone := hsplit (fun _ => 1) (fun _ => 1) fun _ _ _ => rfl
  simp only [one_mul] at hone
  rw [hsplit t u hu, hone, hmain]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
