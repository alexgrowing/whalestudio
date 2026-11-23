import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK kernel4 F0 stdLat alphaQ)

section Gen

variable {L L' : PeriodPair} {ω₀ ω₀' : ℂ}

theorem thetaNull_congr_lattice (h : L.lattice = L'.lattice) (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) :
    Formalism.L2.Th1.F.th0 L (ω₀ / 2) = Formalism.L2.Th1.F.th0 L' (ω₀' / 2) := by
  obtain ⟨-, -, -, hA, -, hs, -⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  have e1 : Formalism.L2.Th1.F.th0 L (ω₀ / 2) = Formalism.L2.Th1.F.th0 L' (ω₀ / 2) := by
    funext z
    simp only [Formalism.L2.Th1.F.th0, Formalism.L2.Th1.F.opU, Formalism.L2.Th1.F.herm, hA, hs]
  rw [e1]
  funext z
  have := Formalism.L2.Th1.F.th0Class L' (ω₀' / 2) ((ω₀ - ω₀') / 2) z hω hn
  rw [← this]
  congr 1
  ring

theorem stdH_congr (h : L.lattice = L'.lattice) (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.L2.Th1.H.stdH L n = Formalism.L2.Th1.H.stdH L' n := by
  unfold Formalism.L2.Th1.H.stdH
  rw [(Formalism.L2.Th1.F.latticeOnly L L' h).2.2.2.1]

theorem hOne_congr (h : L.lattice = L'.lattice) (n : Type) [Fintype n] [DecidableEq n] : hOne L n = hOne L' n := by
  unfold hOne
  rw [(Formalism.L2.Th1.F.latticeOnly L L' h).2.2.2.1]

theorem thM_congr (h : L.lattice = L'.lattice) (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) (c : ℝ)
    {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (κ : ℂ) :
    thM L ω₀ c ΛM g κ = thM L' ω₀' c ΛM g κ := by
  have e : IsThM L ω₀ c ΛM g κ = IsThM L' ω₀' c ΛM g κ := by
    funext θ
    unfold IsThM kernel4 F0 Formalism.L2.Th1.H.stdLat
    rw [hOne_congr h, stdH_congr h, thetaNull_congr_lattice h hω hn, h]
  unfold thM
  rw [e]

end Gen

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def reBase (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) : Base D cc δ :=
  { B with L := L', lat := hl, ω₀ := ω₀', t0 := ht }

theorem lattice_eq (B B' : Base D cc δ) : B.L.lattice = B'.L.lattice := by
  have h : B.L.lattice.toAddSubgroup = B'.L.lattice.toAddSubgroup := B.lat.trans B'.lat.symm
  exact Submodule.toAddSubgroup_injective h

theorem thMM_reBase (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) (hω : (B.ω₀ - ω₀') / 2 ∈ L'.lattice) :
    B.thMM = (reBase B L' hl ω₀' ht).thMM :=
  thM_congr (lattice_eq B (reBase B L' hl ω₀' ht)) hω (Base.half_not_mem (reBase B L' hl ω₀' ht)) _ _ _ _

theorem eNat_reBase (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) (hω : (B.ω₀ - ω₀') / 2 ∈ L'.lattice) (χ : TaylorLogMetric.IdE D → ℂ) :
    B.eNat χ = (reBase B L' hl ω₀' ht).eNat χ := by
  funext N N' L L₁ z
  simp only [Base.eNat, Base.thMoved, Base.thHalf, Base.thZero, thMM_reBase B L' hl ω₀' ht hω]

theorem ambOf_reBase {X : Fields} (s : Seam D X) (B : Base D cc δ) (L' : PeriodPair) (hl : L'.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (ω₀' : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (ω₀' / 2)) (hω : (B.ω₀ - ω₀') / 2 ∈ L'.lattice) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    (ambOf s B χ cD : Amb X) = ambOf s (reBase B L' hl ω₀' ht) χ cD := by
  unfold ambOf
  rw [eNat_reBase B L' hl ω₀' ht hω χ]

section Re

open Formalism.L2.Th1.F (cmTheta)

variable (B : Base D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0)

theorem theta_val' (d : ℕ) : cmTheta 1 d = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
  simp [cmTheta]

theorem mem_lam_iff (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (x : ℂ) :
    x ∈ TaylorLogMetric.lamOf D cc δ ↔ x ∈ (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice := by
  rw [← hl]; rfl

theorem isTorsionPoint_standard_CM (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) :
    GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (lam * a₀ / 2) := by
  obtain ⟨h1, h2, h3⟩ := half_period_standard_CM a₀ b₀ c₀ D.host.d ha hd lam hlam hcm
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - cmTheta 1 D.host.d := by rw [theta_val']; ring
  refine ⟨(mem_lam_iff a₀ b₀ ha hd lam hlam hl _).2 h1, ?_, ?_⟩
  · rw [mem_lam_iff a₀ b₀ ha hd lam hlam hl, ← theta_val']; exact h2
  · rw [mem_lam_iff a₀ b₀ ha hd lam hlam hl, e]; exact h3

def cmBase (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) : Base D cc δ :=
  reBase B (cmL a₀ b₀ D.host.d ha hd lam hlam) hl (lam * a₀) (isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd lam hlam hcm hl)

theorem cmBase_isCm (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) :
    (cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl).IsCm a₀ b₀ ha hd lam hlam := ⟨rfl, rfl⟩

theorem ambOf_cmBase {X : Fields} (s : Seam D X) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    (ambOf s B χ cD : Amb X) = ambOf s (cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl) χ cD := by
  refine ambOf_reBase s B _ hl _ _ ?_ χ cD
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - cmTheta 1 D.host.d := by rw [theta_val']; ring
  have h := half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (B.ω₀ / 2)
    ((mem_lam_iff a₀ b₀ ha hd lam hlam hl _).1 B.t0.1)
    (by rw [← mem_lam_iff a₀ b₀ ha hd lam hlam hl, theta_val']; exact B.t0.2.1)
    (by rw [← mem_lam_iff a₀ b₀ ha hd lam hlam hl, ← e]; exact B.t0.2.2)
  have e2 : (B.ω₀ - lam * a₀) / 2 = B.ω₀ / 2 - lam * a₀ / 2 := by ring
  rw [e2]
  exact h

end Re

end Formalism.L2.Ker.KS
