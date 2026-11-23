import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementD
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 TransInt
  opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH phC)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)

theorem TransIntC_proof : TransIntC := by
  intro p _ L ι hp hW ω₀ hω hω2 s N hN hpN hs
  have h := (Formalism.L2.Th1.E.th0Analytic p L ι hp hW ω₀ hω hω2).2 s N hN hpN hs
  rw [Formalism.L2.Th1.Top.KJ.phC_eq]
  exact h.1

theorem thetaU_one {K : Type} [Field K] (ι : ℂ →+* K) (lg : PowerSeries K) {n : Type} [Fintype n] [DecidableEq n]
    (f : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.thetaU ι lg (1 : Matrix n n K) f =
      MvPowerSeries.subst (fun i => Formalism.InvariantFactorPaths.G7.at1 i lg) (MvPowerSeries.map ι (taylorMv f)) := by
  unfold Formalism.L2.Th1.H.thetaU
  congr 1
  funext i
  simp [Matrix.one_apply]

theorem TensStd_of (hZ : ShapeToZ) (hT : TransIntC) : TensStd := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hok n _ _ h Λ hsd hst θ hθ p _ hp ι hW g₁ ε hiso hnd hrel hε htens t N hN hpN ht
  have hω : (cmL a₀ b₀ dK ha hdK lam hlam).ω₁ = lam * a₀ := by
    first
      | rfl
      | simp [cmL, Formalism.L2.Th1.F.scalePair, Formalism.L2.Th1.F.cmPair]
      | (simp [cmL, Formalism.L2.Th1.F.scalePair, Formalism.L2.Th1.F.cmPair]; ring)
  have hmem : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice :=
    hω ▸ PeriodPair.ω₁_mem_lattice _
  have hnot : lam * (a₀ : ℂ) / 2 ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice :=
    hω ▸ PeriodPair.ω₁_div_two_notMem_lattice _
  have hi1 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := by
    intro h0
    exact hnd (h0 ▸ dvd_zero p)
  have hstd := Formalism.L2.Th1.H.CmData.stdData_cm a₀ b₀ c₀ dK ha hdK lam hlam hok.1 hok.2.1 hok.2.2.1 h Λ g₁
    hiso hsd hst hi1 hrel
  have hTI := hT p (cmL a₀ b₀ dK ha hdK lam hlam) ι hp hW (lam * a₀) hmem hnot
  have hcc : PowerSeries.constantCoeff (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) = 0 := by
    rw [Formalism.L2.Th1.Top.KJ.phC_eq]
    exact Formalism.L2.Th1.E.Tor.cc_phL p _ ι
  have hK := Formalism.L2.Th1.H.quadraticSemicharacters_fact p (cmL a₀ b₀ dK ha hdK lam hlam) ι (lam * a₀) _ _ _
    (Formalism.L2.Th1.C.WeierstrassCurveSeries.logPair _) hcc hTI n h Λ _ _ g₁ hstd hnd ε hε θ hθ htens t N hN hpN ht
    ℂ_[p] (RingHom.id _) (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) 1 (by
      intro a i w
      simp [Matrix.one_apply])
  rw [thetaU_one] at hK
  exact hZ ℂ_[p] _ _ _ (Formalism.L2.Th1.C.WeierstrassCurveSeries.logPair _) hcc n _ _ hK

end Formalism.L2.Th1.GD
