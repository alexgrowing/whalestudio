import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuDegG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.PeriodIntegrals.KFinSmooth

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

def Acc (k r : ℕ) : ℝ := ((64 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ)

theorem AB_le_Acc (k r : ℕ) : B.AB k r ≤ Acc k r := by
  unfold B.AB Acc
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (1 : ℝ) ≤ 2 * r + k + 1 := by linarith
  nlinarith [mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg hk hk, mul_nonneg hr hr,
    mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hr,
    mul_nonneg (mul_nonneg hk hr) hr]

def NormSquareTransferIdentity : Prop :=
  ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F

def CoefCC : Prop :=
  PI.KFinSmooth → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ)
    (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → B.InCC (Acc k r) 5 (A.coef Bs.μG)

def BetaInfAbs : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F →
    Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D F F p) D.μSS →
    B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS

def BetaInfCoef : Prop :=
  SchurH → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ)
    (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → A.l A.w0 ≠ 0 → A.l' A.w0 ≠ 0 →
    Integrable (fun p => B.xiTau Bs (1, 1) p * B.Ph Bs (A.coef Bs.μG) (A.coef Bs.μG) p) Bs.μSS ∧
    ∫ p, B.xiTau Bs (1, 1) p * B.Ph Bs (A.coef Bs.μG) (A.coef Bs.μG) p ∂Bs.μSS = ((A.deg Bs.μG : ℝ) : ℂ)

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem beta_eq_integral (D : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    B.beta D F F = ∫ q, (((Formalism.QuantumDeterminants.bcWeight P.k P.r (Formalism.QuantumDeterminants.Tz P.k P.r D.z) (Formalism.QuantumDeterminants.Tz P.k P.r D.z') q *
      ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 : ℝ)) : ℂ) := by
  unfold B.beta Formalism.QuantumDeterminants.betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem normSq_of_beta (D : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : ℝ) (hx : x ≠ 0)
    (hβ : B.beta D F F = (x : ℂ)) : B.normSq D F = ENNReal.ofReal x := by
  set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q => Formalism.QuantumDeterminants.bcWeight P.k P.r (Formalism.QuantumDeterminants.Tz P.k P.r D.z)
    (Formalism.QuantumDeterminants.Tz P.k P.r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 with hg
  have hβ' := beta_eq_integral D F
  rw [hβ] at hβ'
  have hint : Integrable (fun q => ((g q : ℝ) : ℂ)) := by
    by_contra hn
    rw [integral_undef hn] at hβ'
    exact hx (by exact_mod_cast hβ')
  have hgi : Integrable g := by
    have := hint.re
    simpa using this
  have hx' : x = ∫ q, g q := by
    rw [integral_complex_ofReal] at hβ'
    exact_mod_cast hβ'
  unfold B.normSq Formalism.QuantumDeterminants.jNormSq
  rw [hx', ofReal_integral_eq_lintegral_ofReal hgi
    (Filter.Eventually.of_forall fun q => mul_nonneg (CutBP.bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _))]

theorem normDegG_of_leaves [CompleteSpace Wp] [CompleteSpace Wq] (hJ : NormSquareTransferIdentity) (hC : CoefCC) (hA : BetaInfAbs)
    (hB : BetaInfCoef) (hL : B2.LemmaBAny) (hSch : SchurH) (hK : PI.KFinSmooth) (p : KB.Pl P Wp Wq) :
    NormDegG p := by
  intro F lam0 q0 hF
  obtain ⟨c, hc, -, -, hβ, -, -⟩ := hL P.k P.r Wp Wq p.T.base (Acc P.k P.r) (AB_le_Acc _ _)
  refine ⟨(c : ℝ), by exact_mod_cast hc, fun μ hμ hP => ?_⟩
  have hG := hF μ hμ hP.1
  have hcc := hC hK P.k P.r Wp Wq p.T.base _ _ _ _ _ _ _ (F.A μ) hG
  obtain ⟨hI, hE⟩ := hB hSch P.k P.r Wp Wq p.T.base _ _ _ _ _ _ _ (F.A μ) hG hP.2.1 hP.2.2
  have hinf := hA P.k P.r Wp Wq p.T.base (Acc P.k P.r) _ (AB_le_Acc _ _) hcc hI
  have hdeg : 0 < (F.A μ).deg p.T.base.μG := degPos_of hSch p F lam0 q0 hF μ hμ hP
  have hbeta : B.beta p.T.base (F.J p.T.base μ) (F.J p.T.base μ) =
      (((c : ℝ) * (F.A μ).deg p.T.base.μG : ℝ) : ℂ) := by
    rw [JFam.J_of_hc _ F _ hP.1, hβ _ _ hcc hcc, hinf, hE]
    push_cast
    ring
  rw [hJ P Wp Wq p, normSq_of_beta p.T.base _ _ (mul_pos (by exact_mod_cast hc) hdeg).ne' hbeta]

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG
