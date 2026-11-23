import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

def expG (X : Sys p) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℤ :=
  ∑ v : X.Pl, X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2)

def scalG (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℂ :=
  muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j La))⁻¹ *
    (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j La)) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ))

def AdmG (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    TaylorLogMetric.admitted D _ _ (fd.kerN j L0) (fd.kerN (j + 1) La')

def ScalG (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    scalG fd χ muT j L0 La' ∈ TaylorLogMetric.Qbar ∧
      ‖(p : ℂ_[p]) ^ expG X j L0 La' * TaylorLogMetric.lamC lam (scalG fd χ muT j L0 La')‖ ≤ 1

def K1G : Prop :=
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
      AdmG X hfin D fd → Formalism.L2.KerInert.RepRec.ClAway p cl → Formalism.L2.KerInert.RepRec.XiAway X D Ξ₀ →
      ScalG X hfin fd χ muT lam →
      Formalism.L2.KerInert.RepFrame.LamPosG X E D pos lam ρ → Formalism.L2.KerInert.RepFrame.MInv X fd.frM →
      Formalism.L2.KerInert.RepFrame.FrameLatMap X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ →
      adm2 D X (pendT X E hfin hst hLT pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT))) ∧
      adm2b D X (pendT X E hfin hst hLT pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT))) ∧
      adm3 D X (pendT X E hfin hst hLT pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT)))

end Formalism.L2.KerInert.KG
