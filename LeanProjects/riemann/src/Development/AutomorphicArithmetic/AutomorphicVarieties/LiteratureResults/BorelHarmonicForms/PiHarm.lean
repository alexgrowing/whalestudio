import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasTens
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AbsHarm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PiForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.QdetIntertw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ActOpApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TensDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.InfAbs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem piHarm_abs (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a n : ℕ) (e : Fin n → Herm E a)
    (he : IsFrame e) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (κ : Kinf E a → Module.End ℂ M) (A B : Lie E a →ₗ[ℝ] Module.End ℂ M) (r : ℝ)
    (a1 : IsLieHom A) (b1 : IsLieHom B) (hab : ∀ X Y, Commute (A X) (B Y))
    (a2 : ∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), κ k * A (toL X) = A (toL (k.1 * X * star k.1)) * κ k)
    (b2 : ∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), κ k * B (toL X) = B (toL (k.1 * X * star k.1)) * κ k)
    (hder : SepDer κ (A + B)) (c : ℂ) (hc : ∀ m, (cas (shift B (-r)) e - cas (shift A r) e) m = c • m)
    (hC : HasCohomology κ (A + B)) (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hH : IsPos H ⊤)
    (hadj : ∀ (X : Herm E a) x y, H x ((A + B) (toL X.1) y) = H (adj A B r (toL X.1) x) y)
    (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) (hω : IsCochain κ ω) :
    dCo (A + B) ω = 0 ∧ Coclosed (adj A B r) e ω := by
  obtain ⟨-, -, l3, l4⟩ := ellFacts E a
  have hA := l4 _ A r a1
  have hB := l4 _ B (-r) b1
  have hsum := shift_add_shift A B r
  have hcom : ∀ X Y, Commute (shift A r X) (shift B (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hinf : ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq (shift A r + shift B (-r)) ω := by
    rw [hsum]
    exact infAbs E a M κ (A + B) hder
  have hK : ∀ (k : Kinf E a) (X : Herm E a), κ k * (shift B (-r) - shift A r) (toL X.1) =
      (shift B (-r) - shift A r) (toL (adHerm k X).1) * κ k := fun k X => by
    have e1 : (adHerm k X).1 = k.1 * X.1 * star k.1 := rfl
    rw [e1, LinearMap.sub_apply, LinearMap.sub_apply, shift_apply, shift_apply, shift_apply, shift_apply, l3 k X.1,
      mul_sub, sub_mul, mul_add, mul_add, add_mul, add_mul, a2, b2, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
      smul_mul_assoc, mul_one, one_mul]
  have hc0 : c = 0 := casZero E a n e he M κ _ _ hA hB hcom hK hinf c hc (by rw [hsum]; exact hC)
  have hcas : cas (shift B (-r)) e = cas (shift A r) e :=
    sub_eq_zero.1 (LinearMap.ext fun m => by rw [hc m, hc0, zero_smul]; rfl)
  have := absHarm E a n e he M _ _ hA hB hcom hcas H hH (by rw [hsum]; exact hadj) q ω (hinf q ω hω)
  rw [hsum] at this
  exact this

theorem UpperTheory.V.Lit.Bor.piHarm :
    UpperTheory.V.Lit.Bor.PiHarm := by
  intro E _ _ _ a ha n e he π Ξ r hr hC q ω hω
  obtain ⟨a1, a2, -⟩ := tensA E a π Ξ
  obtain ⟨b1, b2, -⟩ := tensB E a π Ξ
  obtain ⟨c, hc⟩ := casTens E a n e he π Ξ r
  obtain ⟨H, hH, hadj⟩ := piForm E a ha π Ξ r (oneEig E a π Ξ r hr hC)
  exact piHarm_abs E a n e he _ (tensorK π Ξ) (lieA π Ξ) (lieB π Ξ) r a1 b1 (lieA_commute π Ξ) a2 b2
    (tensDer E a π Ξ) c hc hC H hH hadj q ω hω
