import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def absTy (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def ThetaC {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : A :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

def GTCCurvPoly : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel → 2 ≤ P.k →
    d.L.TT = (P.TT : ℂ) →
    MAx3.G.PolyIn (fun u => d.QQ u 0 0 - u ^ (P.k + 1) • (1 : A) - u ^ P.k • ThetaC d) (P.k - 1) ∧
    MAx3.G.PolyIn (fun u => d.QQ u 1 0) P.k

def GTCCurvRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (f g : ℂ → A) (Θ : A), 1 ≤ n →
    (∀ u v : ℂ, (u - v) • (f u * g v - g v * f u) = g u * f v - g v * f u) →
    MAx3.G.PolyIn (fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ) (n - 1) →
    MAx3.G.PolyIn g n → ∀ v, Θ * g v - g v * Θ = - g v

def GTCCurvBlock : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel →
    (∀ v : ℂ, ThetaC d * d.QQ v 1 0 - d.QQ v 1 0 * ThetaC d = - d.QQ v 1 0) →
    ∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
      algebraMap ℂ A ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvIdOfCut : Prop := GTCCurvPoly → GTCCurvRTT → GTCCurvBlock → GTCCurvId

theorem gTCCurvId_of_cut : GTCCurvIdOfCut := by
  intro hPo hR hB Wp Wq _ _ _ _ _ _ P Bs X d hyp ρ
  obtain ⟨hPl, hk, -, hAL, -, hRel, hQQ⟩ := hyp
  have hS : Wd.IsStart d.QQ (M.qC P) := by
    have h0 := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X).1
    rwa [show X.QQ = d.QQ from funext hQQ] at h0
  have hTT : d.L.TT = (P.TT : ℂ) := by
    rw [hAL.2.2.2.2.2.2.2.2.2.2.2.2, Formalism.FourierDecayAlt.P.NFx4.TT_eq hPl]
  obtain ⟨h1, h2⟩ := hPo P _ d hRel hk hTT
  have hc := hR _ P.k (fun u => d.QQ u 0 0) (fun u => d.QQ u 1 0) (ThetaC d) (by omega)
    (fun u v => Formalism.FourierDecayAlt.P.NFx4.SX.rtt_ent d hS u v 0 0 1 0) h1 h2
  exact hB P _ d hRel hc ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
