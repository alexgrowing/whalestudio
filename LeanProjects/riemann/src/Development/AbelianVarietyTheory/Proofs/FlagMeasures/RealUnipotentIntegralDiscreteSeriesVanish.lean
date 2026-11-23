import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishes

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma prod_mul_mulSingle_mul {ι : Type*} [Fintype ι] {dec : DecidableEq ι} {G : ι → Type*}
    [∀ i, Group (G i)] (f : ∀ i, G i → ℂ) (a b : ∀ i, G i) (v : ι) (m : G v) :
    ∏ u, f u (a u * Pi.mulSingle v m u * b u) =
      f v (a v * m * b v) * ∏ u ∈ Finset.univ.erase v, f u (a u * b u) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Pi.mulSingle_eq_same]
  congr 1
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]

theorem integral_phe_eq_zero_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  intro B d h hDS hK hLoc hh v Wv hW ν hν x y
  obtain ⟨-, hds, hlow, hfd⟩ := hDS v
  have hU := hds.2.2.1
  obtain ⟨α, hαs, hαc, hαf⟩ :=
    exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU (hK v)
  have hq : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn : 1 ≤ B.I.n := by
    have hle : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    omega
  obtain ⟨h0, hc⟩ := rate_lt hn hq (hh v)

  have hF := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v)))) α (B.w v) hU hfd (by exact_mod_cast hc) hlow.1 hαs hαc
    (fun u => hαf (B.w v) hlow.2 u)
    ⟨Real.exp (h / 8), fun g => (hLoc v g).trans (decE_le_exp hq h0 _)⟩ (x.1 v) (y.1 v)

  have hpt : ∀ m : UJ (B.I.ε v), phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
      (open Classical in (((∏ u, d u : ℝ) : ℂ) *
        star (∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ) *
        B.e (x.2 * y.2))) * star ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    simp only [phe, ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [prod_mul_mulSingle_mul (fun u g => ⟪B.w u, B.σ u (uMat g) (B.w u)⟫_ℂ) x.1 y.1 v m, star_mul]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hconj : ∫ m, star ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν =
      star (∫ m, ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν) := integral_conj
  rw [hconj, hF, star_zero, mul_zero]

end GlobalTheory.RealFibre
