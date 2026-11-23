import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliDetAdInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP

theorem thr_of_budget (k r : ℕ) (N A₀ : ℝ) (hk : 2 ≤ k) (hN : 0 ≤ N)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * (N * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    JF.TransportedAlt k r A₀ (2 * r + k + 1) := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  rw [hcast, lt_div_iff₀ (by positivity)]
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    calc (r : ℝ) + 1 = ((r : ℝ) + 1) * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ 3 := by gcongr
      _ = ((r : ℝ) + 1) ^ 4 := by ring
  have h3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 = n ^ 2 * 1 := by ring
      _ ≤ n ^ 2 * n := by gcongr
      _ = n ^ 3 := by ring
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  have hstep : 100 * ((r : ℝ) + 1) * n ^ 2 ≤ A₀ := by
    calc 100 * ((r : ℝ) + 1) * n ^ 2 ≤ 100 * ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
          have : ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
            calc ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * n ^ 2 := by gcongr
              _ ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by gcongr; linarith
          linarith
      _ ≤ A₀ := hA
  have hrn : (r : ℝ) * n ≤ ((r : ℝ) + 1) * n ^ 2 := by
    have : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
    calc (r : ℝ) * n ≤ ((r : ℝ) + 1) * n := by gcongr
      _ = ((r : ℝ) + 1) * n * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * n * n := by gcongr
      _ = ((r : ℝ) + 1) * n ^ 2 := by ring
  have hpos : 0 < ((r : ℝ) + 1) * n ^ 2 := by positivity
  nlinarith

theorem bessel_eigenvalue_equation_holds : BesselEigen := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Y x hx
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, heig⟩ := hv v
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hplace.2.2.2.2.1
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hg : B.gq (T v).base x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' :=
    Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base x hq
  have hgG : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) (B.gq (T v).base x) =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) (B.gq (T v).base x)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
