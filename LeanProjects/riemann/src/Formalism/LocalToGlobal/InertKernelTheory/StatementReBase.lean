import Formalism.LocalToGlobal.InertKernelTheory.StatementKap

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm IsFrameH thetaH uniformGaussModelCondition)
open Formalism.L2.Th1.H (CmOK matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4)

def ThMMReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0) (B' : Base D cc δ),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ B'.IsCm a₀ b₀ ha hd ((g : ℂ) * δ) hl ∧
      B'.L.lattice = B.L.lattice ∧ B'.γ₀ = B.γ₀ ∧ B'.gC = B.gC ∧ B'.kappa = B.kappa ∧
      (B.ω₀ - B'.ω₀) / 2 ∈ B.L.lattice ∧ B'.IsThMM = B.IsThMM ∧ B'.thMM = B.thMM

def FirstKernelThetaAllBases : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 → ∀ ι : ℂ ≃+* ℂ_[l],
    ∃ g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
      StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
        (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g ∧
      ¬ l ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ∧
      ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, IsLTNorm l B.L ι g2 g3 s2 ε → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
        ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1 → ‖ε‖ = 1 →
        (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
      ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ B.lamM →
      ∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension l))
        (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[l]),
        IsFrameH σ ι g γ B' → uniformGaussModelCondition l g2 g3 s2 ε (thetaH l ι B' (hOne B.L D.what₂.Tau) t B.thMM) γ

end Formalism.L2.KerInert
