import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

section defs

variable {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Lf (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp) (x : Mt k r × Mt k r) : ℂ :=
  ⟪ξ, D.π (Matrix.of x.1) ξ⟫_ℂ * ⟪σ (Matrix.of x.2 * Matrix.of x.1) v, v⟫_ℂ

def Rf (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq) (x : Mt k r × Mt k r) : ℂ :=
  ⟪ξ', D.π' (Matrix.of x.1)⁻¹ ξ'⟫_ℂ * ⟪v', σ (Matrix.of x.2 * Matrix.of x.1) v'⟫_ℂ

def H1 (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp) (x : Mt k r × Mt k r) (t : ℝ) : ℂ :=
  ((D.χ t * t ^ kap k r : ℝ) : ℂ) * Lf D σ v ξ (x.1, conjM (aDil k r t) x.2)

def H2 (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq) (x : Mt k r × Mt k r) (t : ℝ) : ℂ :=
  ((D.χ t * t ^ kap k r : ℝ) : ℂ) * Rf D σ v' ξ' (x.1, conjM (aDil k r t) x.2)

def I1 (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp) (x : Mt k r × Mt k r) : ℂ :=
  ∫ t : ℝ, H1 D σ v ξ x t * Complex.exp (Complex.I * ((lam k r D.z (Matrix.of x.2) * t : ℝ) : ℂ))

def I2 (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq) (x : Mt k r × Mt k r) : ℂ :=
  ∫ t : ℝ, H2 D σ v' ξ' x t * Complex.exp (Complex.I * ((-lam k r D.z' (Matrix.of x.2) * t : ℝ) : ℂ))

end defs

def PhiAt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lm : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lm → PI.UpqRep.IsDSHpk k r ε lm σ →
    ∃ d : ℝ, 0 < d ∧ ∀ (v v' : H) (ξ : Wp) (ξ' : Wq) (p : SS k r), D.inSS p → ∀ t : ℝ × ℝ, 0 < t.1 → 0 < t.2 →
      Ph D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') (dilation₂ t p) =
        (d : ℂ)⁻¹ * Lf D σ v ξ (p.1.1, conjM (aDil k r t.1) p.1.2) * Rf D σ v' ξ' (p.2.1, conjM (aDil k r t.2) p.2.2)

def LeftProfileContDiffTwo : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lm : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lm → PI.UpqRep.IsDSHpk k r ε lm σ → ∀ (v : H) (ξ : Wp), v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
    ∀ x : Mt k r × Mt k r, Matrix.of x.1 ∈ UWset k r D.z → Matrix.of x.2 ∈ Nset k r → ContDiff ℝ 2 (H1 D σ v ξ x)

def RightProfileContDiffTwo : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lm : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lm → PI.UpqRep.IsDSHpk k r ε lm σ → ∀ (v' : H) (ξ' : Wq), v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
    ∀ x : Mt k r × Mt k r, Matrix.of x.1 ∈ UWset k r D.z' → Matrix.of x.2 ∈ Nset k r → ContDiff ℝ 2 (H2 D σ v' ξ' x)

def BetaFactor : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lm : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lm → PI.UpqRep.IsDSHpk k r ε lm σ →
    ∃ d : ℝ, 0 < d ∧ ∀ (v v' : H) (ξ : Wp) (ξ' : Wq),
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
      betaInf D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') =
        (d : ℂ)⁻¹ * (∫ x, I1 D σ v ξ x ∂(D.μW.prod D.μN)) * (∫ x, I2 D σ v' ξ' x ∂(D.μW'.prod D.μN))

def LeftLimit : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lm : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lm → PI.UpqRep.IsDSHpk k r ε lm σ → ∀ (v : H) (ξ : Wp), v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
    Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v) (D.μW.prod D.μN) →
    ∫ x, I1 D σ v ξ x ∂(D.μW.prod D.μN) = star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.be D.z cStd D.π σ D.μW D.μN v v ξ⟫_ℂ

def RightLimit : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lm : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsHCParam lm → PI.UpqRep.IsDSHpk k r ε lm σ → ∀ (v' : H) (ξ' : Wq), v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
    Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' cStd D.π' σ v' v') (D.μW'.prod D.μN) →
    ∫ x, I2 D σ v' ξ' x ∂(D.μW'.prod D.μN) = ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.be D.z' cStd D.π' σ D.μW' D.μN v' v' ξ'⟫_ℂ

theorem integrable_of_be_eq {k r : ℕ} {Wp H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (σ : Mat k r → (H →L[ℂ] H))
    (μW μN : Measure (Mt k r)) (v : H) (w ξ : Wp)
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be z cStd π σ μW μN v v = (innerSL ℂ w).smulRight w) (hw : ⟪w, ξ⟫_ℂ ≠ 0) :
    Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z cStd π σ v v) (μW.prod μN) := by
  by_contra hI
  have h0 : Formalism.FourierDecayAlt.ThreeDimData.be z cStd π σ μW μN v v = 0 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.be
    exact integral_undef hI
  rw [hbe] at h0
  have h1 := congrArg (fun T : Wp →L[ℂ] Wp => T ξ) h0
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.zero_apply] at h1
  have hw0 : w = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h hw
    · exact h
  exact hw (by rw [hw0, inner_zero_left])

theorem betaInfCoefNZ_of (hF : BetaFactor) (hL : LeftLimit) (hR : RightLimit) :
    Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ h hHC hDS hGap hOK v v' l l' ξ ξ' hv hv' hbe hbe' h1 h2
  obtain ⟨d, hd, hfac⟩ := hF k r Wp Wq D ε lm H σ hHC hDS
  have hI : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v) (D.μW.prod D.μN) :=
    integrable_of_be_eq D.z D.π σ D.μW D.μN v (l v) ξ hbe h1
  have h2' : ⟪l' v', ξ'⟫_ℂ ≠ 0 := by
    rw [← inner_conj_symm]; exact (map_ne_zero _).mpr h2
  have hI' : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' cStd D.π' σ v' v') (D.μW'.prod D.μN) :=
    integrable_of_be_eq D.z' D.π' σ D.μW' D.μN v' (l' v') ξ' hbe' h2'
  rw [hfac v v' ξ ξ' hv hv', hL k r Wp Wq D ε lm H σ hHC hDS v ξ hv hI,
    hR k r Wp Wq D ε lm H σ hHC hDS v' ξ' hv' hI', hbe, hbe']
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
  have hd0 : ((d : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
  have h1' : ⟪ξ, l v⟫_ℂ ≠ 0 := by
    rw [← inner_conj_symm]; exact (map_ne_zero _).mpr h1
  refine mul_ne_zero (mul_ne_zero hd0 ?_) (mul_ne_zero h2' h2)
  exact (star_ne_zero).mpr (mul_ne_zero h1 h1')

end PI.BICNZ
