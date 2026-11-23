import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuDeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuHC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def DegHC (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    (F.A μ).deg p.T.base.μG = C * PI.UpqRep.fdegHC (lamOf F.sh μ)

def FdegHpkHC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w : H),
      Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → w ≠ 0 →
      PI.BesselPeriodGGP.fdegH μG σ w = C * PI.UpqRep.fdegHC lam

theorem lamOf_add_eI {n : ℕ} (sh : ℝ) (μ : Fin n → ℤ) (I : Finset (Fin n)) :
    lamOf sh (μ + LatticeNorms.eI I) = fun i => lamOf sh μ i + if i ∈ I then 1 else 0 := by
  funext i
  simp only [lamOf, LatticeNorms.eI, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

theorem fdegHC_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  refine div_nonneg (prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _)
    (prod_nonneg fun a _ => prod_nonneg fun b hb => ?_)
  have := (mem_filter.1 hb).2
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem degRatio_of (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ)
    (hHC : DegHC p F lam0 q0) : DegRatio p F lam0 q0 := by
  intro μ I hI hμ hμI hp hq
  obtain ⟨C, hC, hd⟩ := hHC
  rw [hd _ hμI hq, hd μ hμ hp, lamOf_add_eI]
  have hinj : Function.Injective (lamOf F.sh μ) := hp.1.1.injective
  have hint : ∀ a b, ∃ m : ℤ, lamOf F.sh μ a - lamOf F.sh μ b = m := by
    intro a b
    obtain ⟨ma, ha⟩ := hp.1.2 a
    obtain ⟨mb, hb⟩ := hp.1.2 b
    exact ⟨ma - mb, by push_cast; linarith⟩
  have hb := JmuHC.fdegHC_addI_le (lamOf F.sh μ) hinj hint I
  rw [hI] at hb
  have hf0 := fdegHC_nonneg (lamOf F.sh μ)
  have hn : ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ (P.r + 1) ≤ (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    have he : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    nlinarith [(Nat.cast_nonneg (2 * P.r + P.k + 1) : (0 : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ))]
  calc C * PI.UpqRep.fdegHC (fun i => lamOf F.sh μ i + if i ∈ I then 1 else 0)
      ≤ C * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ (P.r + 1) * PI.UpqRep.fdegHC (lamOf F.sh μ)) :=
        mul_le_mul_of_nonneg_left (by simpa using hb) hC.le
    _ ≤ C * ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * PI.UpqRep.fdegHC (lamOf F.sh μ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn hf0) hC.le
    _ = _ := by ring

theorem degPos_of [CompleteSpace Wp] [CompleteSpace Wq] (hSch : SchurH) (p : KB.Pl P Wp Wq)
    (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) (hF : F.Good p.T.base lam0 q0) :
    DegPos p F lam0 q0 := by
  intro μ hμ hp
  have hG := hF μ hμ hp.1
  obtain ⟨d, hd, hS⟩ := hSch _ _ F.ε (lamOf F.sh μ) (F.A μ).H (F.A μ).σ p.T.base.μG hG.1.1 hG.1.2.1
    hG.1.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨P0, -, hw1, -⟩ := hG.1.2.2.2.2.1
  have hw0 : (F.A μ).w0 ≠ 0 := fun h => by rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  show 0 < PI.BesselPeriodGGP.fdegH p.T.base.μG (F.A μ).σ (F.A μ).w0
  rw [Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd hS hw0]
  exact hd

theorem degree_bound_of_holomorphic_continuation [CompleteSpace Wp] [CompleteSpace Wq] (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq)
    (lam0 : Fin (2 * P.r + P.k + 1) → ℤ)
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (c0 q0 : ℕ) (H : ℝ)
    (hc0 : P.r + 1 ≤ c0) (hN : NormDeg p F lam0 q0) (hSch : SchurH) (hHC : DegHC p F lam0 q0)
    (hF : F.Good p.T.base lam0 q0) (hP0 : Present F lam0) : PieriDegreeConditions p (pieriDataOfFamily p F lam0 tau c0 q0 H) :=
  pieri_degree_of_family p F lam0 tau c0 q0 H hc0 hN (degPos_of hSch p F lam0 q0 hF) (degRatio_of p F lam0 q0 hHC) hP0

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
