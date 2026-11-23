import Formalism.LocalToGlobal.InertKernelTheory.ScalG
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepLt

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KGLt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

def XiAwayLt {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) : Prop :=
  ∃ S₀ : Finset ℕ, p ∉ S₀ ∧ ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 → ∀ y, IntOff S₀ (Ξ j L0 La' y)

def TranslatesOfInertKernelAtPlace : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
      (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
      (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
      (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
      (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
      (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
      (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v),
      GL3Theta.At D cc δ g → GL3Theta.InertK D p → GL3Theta.ModelOverW g.lam g.abelian₂ g.C →
      TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
      lam = g.lam → g.abelian₂ = B.tor.abelian₂ →
      Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd → Formalism.L2.KerInert.RepRec.ClAway p cl →
      XiAwayLt X hfin D Ξ₀ →
      Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT lam →
      Formalism.L2.KerInert.RepFrame.LamPosG X E D pos lam ρ → Formalism.L2.KerInert.RepFrame.MInv X fd.frM →
      Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ →
      adm2 D X (pendT X E hfin hst hLT pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT))) ∧
      adm2b D X (pendT X E hfin hst hLT pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT))) ∧
      adm3 D X (pendT X E hfin hst hLT pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT)))

end Formalism.L2.KerInert.KGLt
