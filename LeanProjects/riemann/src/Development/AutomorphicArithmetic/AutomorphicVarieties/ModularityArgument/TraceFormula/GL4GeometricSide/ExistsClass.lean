import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisRepresentationAdmitted
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GKCoh MeasureTheory GlobalTheory.CompanionTheory.TwY.ThInv
open PositivityTheory.Rg.BcB (thetaA)

private theorem exists_class (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
    (hπ : GlobalTheory.DiscSpec.IsNormalised π) :
    ∃ B : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (B φ ψ) = B ψ φ) ∧ (∀ φ, 0 ≤ (B φ φ).re) ∧
      (∀ φ, φ ≠ 0 → 0 < (B φ φ).re) ∧ (∀ (X : Lie E n) φ ψ, B (lieOp π X φ) ψ + B φ (lieOp π X ψ) = 0) ∧
      ∀ (g : GA E n) (φ ψ φ' ψ' : π.V), (∀ x, φ'.1.1 x = φ.1.1 (x * g)) → (∀ x, ψ'.1.1 x = ψ.1.1 (x * g)) →
        B φ' ψ' = B φ ψ := by
  obtain ⟨μ, hμ, hμ'⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E n
  have hl := GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E n) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have inj : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level
  have sq : ∀ φ : π.V, (inner ℂ (toL2ₗ μ π.V hm φ) (toL2ₗ μ π.V hm φ)).re = ‖toL2ₗ μ π.V hm φ‖ ^ 2 := fun φ =>
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  refine ⟨((innerₛₗ ℂ).comp (toL2ₗ μ π.V hm)).compl₂ (toL2ₗ μ π.V hm), fun φ ψ =>
    inner_conj_symm (𝕜 := ℂ) (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ), fun φ => ?_,
    fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_⟩
  · exact (sq φ).symm ▸ sq_nonneg _
  · exact (sq φ).symm ▸ pow_pos (norm_pos_iff.2 fun e => hφ (inj (e.trans (map_zero _).symm))) 2
  · have e := GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint E n μ π hm (fun φ hφ => (hl φ hφ).2) X ψ φ
    exact (add_comm _ _).trans (add_eq_zero_iff_eq_neg.2 e)
  · change inner ℂ (hm _ φ'.2).toL2 (hm _ ψ'.2).toL2 = inner ℂ (hm _ φ.2).toL2 (hm _ ψ.2).toL2
    rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, funext h, funext h']
    exact GlobalTheory.CompanionTheory.PeterssonSkew.pet_mul_right μ (hm _ ψ.2) (hm _ φ.2) g

theorem UpperTheory.V.Z.GSp4Splitting.petEx :
    PetEx := by
  intro E _ _ _ n _ π hθ
  obtain ⟨B, hc, h0, hp, hL, hg⟩ := exists_class E n π hθ.1
  have hv := thV_apply π hθ
  set T := thV π hθ
  have hTL : ∀ (X : Lie E n) (φ : π.V), T (lieOp π X φ) = -lieOp π (adjH X) (T φ) := fun X φ => by
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have e : φ.1.1 = fun y => (T φ).1.1 (thetaA E n y) := funext fun y => by
      rw [hv, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    have e2 := lieD_theta X (T φ).1.2 (thetaA E n x)
    rw [← e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol] at e2
    exact (hv _ x).trans e2
  have ev : ∀ φ ψ, (B + (B.comp T).compl₂ T) φ ψ = B φ ψ + B (T φ) (T ψ) := fun _ _ => rfl
  refine ⟨B + (B.comp T).compl₂ T, fun φ ψ => ?_, fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_,
    fun φ ψ φ' ψ' h h' => ?_⟩
  · rw [ev, ev, map_add, hc, hc]
  · rw [ev, Complex.add_re]
    exact add_pos_of_pos_of_nonneg (hp φ hφ) (h0 _)
  · have e1 := hL X φ ψ
    have e2 := hL (adjH X) (T φ) (T ψ)
    rw [ev, ev, hTL, hTL, map_neg, map_neg, LinearMap.neg_apply]
    linear_combination e1 - e2
  · rw [ev, ev, hg g φ ψ φ' ψ' h h', hg (thetaA E n g) (T φ) (T ψ) (T φ') (T ψ')] <;> intro x
    · rw [hv, hv, h, map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    · rw [hv, hv, h', map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · have k : ∀ a a' : π.V, (∀ x, a'.1.1 x = a.1.1 (thetaA E n x)) → T a = a' ∧ T a' = a := fun a a' e =>
      ⟨Subtype.ext (Subtype.ext (funext fun x => (hv a x).trans (e x).symm)),
        Subtype.ext (Subtype.ext (funext fun x => by rw [hv, e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]))⟩
    rw [ev, ev, (k _ _ h).1, (k _ _ h).2, (k _ _ h').1, (k _ _ h').2, add_comm]
