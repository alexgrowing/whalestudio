import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.FamilyGapImplicationHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.SIntShiftEqSmul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.HpkMulVecMulVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayley
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.ClmInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.IsClosedUWset

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopNV

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BesselNVUnder (Gap : ℕ → ∀ r : ℕ, (Fin (2 * r + 2) → ℝ) → Prop) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b →
    Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b → Gap k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Formalism.MainNotions.CayleySignature.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Formalism.MainNotions.CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
  ∀ w : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Formalism.MainNotions.CayleySignature.Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
          star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

def BesselNVG : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b →
    Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b → Formalism.MainNotions.CayleySignature.GapBig k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Formalism.MainNotions.CayleySignature.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Formalism.MainNotions.CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
  ∀ w : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Formalism.MainNotions.CayleySignature.Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
          star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

def BesselNV0 : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b →
    Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Formalism.MainNotions.CayleySignature.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Formalism.MainNotions.CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
  ∀ w : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Formalism.MainNotions.CayleySignature.Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
          star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

theorem urep_of_isDSHpk {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}
    (hd : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := by
  obtain ⟨P, hP, hDS⟩ := hd
  have h1 : P⁻¹ * P = 1 := bridge_inv_mul k r ε P hP
  have hback : (fun g => σ (P⁻¹ * (P * g * P⁻¹) * P)) = σ := by
    funext g
    have : P⁻¹ * (P * g * P⁻¹) * P = g := by
      calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [this]
  have := ReciprocityTheory.ChartRestriction.DS.isURepOn_UH_of hP hDS.2.2.1
  rwa [hback] at this

theorem inner_shift {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ)
    {x₀ g x : Mat k r} (hx₀ : x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (w : H) :
    ⟪σ x₀ w, σ g (σ x w)⟫_ℂ = ⟪w, σ (x₀⁻¹ * (g * x)) w⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hnorm, -⟩ := hσ
  have hinv : x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := S0.Core.inv_mem_UH k r x₀ hx₀
  have hgx : g * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := S0.Core.mul_mem_UH k r hg hx
  have hxx : x₀ * x₀⁻¹ = 1 := S0.Core.mul_inv_UH k r hx₀
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ x₀ : H →ₗ[ℂ] H), norm_map' := hnorm x₀ hx₀ }
  have key : σ x₀ (σ x₀⁻¹ (σ (g * x) w)) = σ (g * x) w := by
    have hc := hmul x₀ hx₀ x₀⁻¹ hinv
    rw [hxx, h1] at hc
    have := congrArg (fun A : H →L[ℂ] H => A (σ (g * x) w)) hc
    simpa using this.symm
  calc ⟪σ x₀ w, σ g (σ x w)⟫_ℂ = ⟪σ x₀ w, σ (g * x) w⟫_ℂ := by
        simp only [hmul g hg x hx, ContinuousLinearMap.comp_apply]
    _ = ⟪f w, f (σ x₀⁻¹ (σ (g * x) w))⟫_ℂ := by
        change _ = ⟪σ x₀ w, σ x₀ (σ x₀⁻¹ (σ (g * x) w))⟫_ℂ
        rw [key]
    _ = ⟪w, σ x₀⁻¹ (σ (g * x) w)⟫_ℂ := f.inner_map_map _ _
    _ = ⟪w, σ (x₀⁻¹ * (g * x)) w⟫_ℂ := by
        simp only [hmul x₀⁻¹ hinv (g * x) hgx, ContinuousLinearMap.comp_apply]

theorem besselNVG_of (hB : BAtTargetStatement) (hSZ : SigZeroStatement) : BesselNVG := by
  intro k r z c u v b hk2 hke hz hT hc hu hlam hint hhalf hgap H _ _ _ σ hd Vp _ _ _ π hπ w hw μW μN hμW hμN
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  have hset48 : Formalism.MainNotions.CayleySignature.RealPlaceNumericalSetting k r z c u v b :=
    ⟨by omega, hke, hz, hT, hc, hu, hlam, hint, hhalf, hgap⟩
  obtain ⟨h, hset⟩ := gapBig_gapLap k r z c u v b hset48
  have hgl := hset.2.2.2.2.2.2.2.2.2.2
  obtain ⟨H₀, i₁, i₂, i₃, σ₀, hd₀, -, hcoef⟩ := hSZ k r z c u v b h hset
  have hσU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := urep_of_isDSHpk hd
  obtain ⟨P, hP, hDS⟩ := hd
  obtain ⟨P', hP', hlow⟩ := hw
  obtain ⟨P₀, hP₀, hDS₀⟩ := hd₀
  have hDS' := (cayleyIndep k r _ _ H σ P P' hP hP' hDS).1
  have hDS₀' := (cayleyIndep k r _ _ H₀ σ₀ P₀ P' hP₀ hP' hDS₀).1
  obtain ⟨w₀, hlow₀, hsame⟩ := dsUniv (2 * r + k + 1) _ _ hlam h hgl H (fun g => σ (P'⁻¹ * g * P'))
    H₀ (fun g => σ₀ (P'⁻¹ * g * P')) hDS' hDS₀' w hlow
  have hcoefUH : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ⟪w₀, σ₀ g w₀⟫_ℂ = ⟪w, σ g w⟫_ℂ := by
    intro g hg
    obtain ⟨hgJ, hback⟩ := bridge_conj k r _ P' hP' g hg
    have hg' := hsame _ hgJ
    rwa [hback] at hg'
  obtain ⟨-, -, T, μ, P₁, v₁, c₁, hv₁, hc₁, hμ, hP₁, hpsi⟩ := hcoef w₀ ⟨P', hP', hlow₀⟩
  have hBD : IsBData z c u π μW μN := ⟨hz, hT, hc, hπ, hμW, hμN⟩
  obtain ⟨ξ, x₀, x, hx₀, hx, hne⟩ := hB k r z c u v b h hset T μ P₁ z c Vp π μW μN hμ hP₁ hBD v₁ hv₁
  have hshift := sInt_shift_eq_smul z μW μN hμW hμN (Formalism.MainNotions.S.psiGen k r z c) π
    (fun y => ⟪w, σ y w⟫_ℂ) (psiCoef T μ P₁ v₁ v₁) c₁
    (fun y hy => by rw [← hcoefUH y hy]; exact hpsi y hy) ξ x₀ x hx₀ hx
  have hS : sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π (fun y => ⟪w, σ (x₀⁻¹ * y) w⟫_ℂ) ξ x ≠ 0 := by
    rw [hshift]
    exact smul_ne_zero hc₁ hne
  obtain ⟨hA, huA⟩ := TopPi.piInv_facts z u π μW μN hz hT hπ hμW hμN
  refine ⟨x, x₀, hx, hx₀, ?_⟩
  refine TopClm.integral_ne_zero_of_apply (μ := μW.prod μN)
    (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
        star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2)))
    (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p.1)⁻¹) hA huA ξ ?_
  have := hμW.1
  have := hμN.1
  have hae₁ : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hμW.2.2.1)
  have hae₂ : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hμN.2.2.1)
  have heq : (∫ p, (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
      star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ ξ ∂(μW.prod μN)) =
      sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π (fun y => ⟪w, σ (x₀⁻¹ * y) w⟫_ℂ) ξ x := by
    unfold sInt chiInv
    refine integral_congr_ae ?_
    filter_upwards [hae₁, hae₂] with p h₁ h₂
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      S0.Core.mul_mem_UH k r h₁.1 h₂.1
    rw [inner_shift hσU hx₀ hg hx w, mul_smul]
  rw [heq]
  exact hS

end ReciprocityTheory.ChartRestriction.DS.Lap.TopNV
