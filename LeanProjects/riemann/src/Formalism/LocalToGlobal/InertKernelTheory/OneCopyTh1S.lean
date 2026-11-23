import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm phL)

def OneCopyTh1S : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∃ (c : ℂ) (hc : c ≠ 0) (g2 g3 ε s2 : MaximalUnramifiedExtension p) (σ : ℂ_[p] →+* ℂ_[p]) (r : ℕ)
      (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p])) (e : D.what₂.Tau ≃ Fin r),
      IsLTNorm p (Formalism.L2.Th1.F.scalePair B.L c hc) ι g2 g3 s2 ε ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧
      ‖(g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2‖ = 1 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) ∧
      IsConjP D lam σ ∧ IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v ∧
      ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ B.lamM →
        Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries D.what₂.Tau ℂ_[p]) *
          ReadTh1 p (fun τ j => (ι c)⁻¹ * v (e j) (τ, 0, 0))
            (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
              (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM))))

def IsomStd (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ) : Prop :=
  Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.matH (Formalism.L2.Th1.H.blk4 (hOne B.L D.what₂.Tau)))
            (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) ∧
    ¬ p ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
      (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) ∧
    Formalism.L2.Th1.H.relIdx
      (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))
      (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 ∧
    ‖ι e‖ ≤ 1 ∧
    Formalism.L2.Th1.H.tens4 B.thMM = e • Formalism.L2.Th1.H.kernel4 B.L B.ω₀ B.lamM
      (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g₁

def ScaleLTB : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (c : ℂ) (hc : c ≠ 0) (g2 g3 ε s2 : MaximalUnramifiedExtension p),
      IsLTNorm p (Formalism.L2.Th1.F.scalePair B.L c hc) ι g2 g3 s2 ε ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧
      ‖(g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2‖ = 1 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) ∧
      ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ → ∀ α : MaximalUnramifiedExtension p, ‖α‖ = 1 → σ (σ α) = α →
        Formalism.L2.Th1.D.NormRel p σ (Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) α

def IsomONB : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∃ (g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
      (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension p)) (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[p])
      (σp : ℂ_[p] →+* ℂ_[p]),
      IsomStd D B p ι g₁ e ∧ Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ ∧ Formalism.L2.Th1.Top.IsFrameH σ ι g₁ γ B' ∧
      IsConjP D lam σp ∧
      IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σp
        (fun i k => B' k.1 ((Fintype.equivFin D.what₂.Tau).symm i))

def ScaleInt : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ ι : ℂ ≃+* ℂ_[p],
    ∀ (c : ℂ) (hc : c ≠ 0) (g2 g3 ε s2 : MaximalUnramifiedExtension p),
      IsLTNorm p (Formalism.L2.Th1.F.scalePair B.L c hc) ι g2 g3 s2 ε → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 →
      ‖(g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2‖ = 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) →
    ∀ (g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ), IsomStd D B p ι g₁ e →
    ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ →
      (∀ α : MaximalUnramifiedExtension p, ‖α‖ = 1 → σ (σ α) = α → Formalism.L2.Th1.D.NormRel p σ (Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) α) →
    ∀ (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension p)) (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[p]),
      Formalism.L2.Th1.Top.IsFrameH σ ι g₁ γ B' →
    ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ B.lamM →
      Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries D.what₂.Tau ℂ_[p]) *
        ReadTh1 p (fun τ j => (ι c)⁻¹ * B' τ j)
          (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
            (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM))))

def ModelTieS : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ (c : ℂ) (hc : c ≠ 0) (g2 g3 ε s2 : MaximalUnramifiedExtension p), IsLTNorm p (Formalism.L2.Th1.F.scalePair B.L c hc) ι g2 g3 s2 ε →
      ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖(g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2‖ = 1 → ‖ε‖ = 1 →
      (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) →
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam B.tor.abelian₂ C → IsWq (C • wModel lam B.tor.abelian₂) wq →
      PowerSeries.constantCoeff (phL p g2 g3 s2 ε) = 0 ∧
      ∃ h Uu : PowerSeries ℂ_[p], PowerSeries.constantCoeff h = 0 ∧ (∀ n, IsIntP (PowerSeries.coeff n h)) ∧
        ‖PowerSeries.coeff 1 h‖ = 1 ∧
        PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * (flog (C • wModel lam B.tor.abelian₂) wq).subst h =
          PowerSeries.C (ι c)⁻¹ * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p ∧
        (∀ n, IsIntP (PowerSeries.coeff n Uu)) ∧
        (ePhi1 lam B.tor.abelian₂ C wq)⁻¹.subst h = Uu * (Formalism.DworkPowerSeriesWeights.mvExp (phL p g2 g3 s2 ε) : PowerSeries ℂ_[p])

def ReadChangeS : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (ph h Uu : PowerSeries ℂ_[p]) (κ : ℂ_[p]),
    PowerSeries.constantCoeff ph = 0 →
    PowerSeries.constantCoeff h = 0 → (∀ n, IsIntP (PowerSeries.coeff n h)) → ‖PowerSeries.coeff 1 h‖ = 1 →
    PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * (flog (C • wModel lam Λ) wq).subst h =
      PowerSeries.C κ * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p →
    (∀ n, IsIntP (PowerSeries.coeff n Uu)) →
    (ePhi1 lam Λ C wq)⁻¹.subst h = Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p]) →
    ∀ (r : ℕ) (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p])) (e : D.what₂.Tau ≃ Fin r)
      (F : MvPowerSeries D.what₂.Tau ℂ_[p]),
      Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) *
        ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F) →
      IntegralMv (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)

end Formalism.L2.KerInert
