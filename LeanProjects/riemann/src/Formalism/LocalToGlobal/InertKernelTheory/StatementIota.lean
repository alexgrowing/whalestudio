import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

def IotaExt {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  ∀ x : Formalism.MainNotions.TaylorLogMetric.Qbar, ι (x : ℂ) = lam x

def taylorSer (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ :=
  fun α => Formalism.MainNotions.TaylorLogMetric.taylor D G α

def AlgCoef (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) : Prop :=
  ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D G α ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

def LamExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]), ∃ ι : ℂ ≃+* ℂ_[p], IotaExt lam ι

def LamCIota : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    (∀ x : ℂ, x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar → Formalism.MainNotions.TaylorLogMetric.lamC lam x = ι x) ∧
    (∀ x : ℂ, x ∉ Formalism.MainNotions.TaylorLogMetric.Qbar → Formalism.MainNotions.TaylorLogMetric.lamC lam x = 0)

def PSerIota : Prop :=
  ∀ (D : D7) (N N' p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ, AlgCoef D G →
      Formalism.MainNotions.TaylorLogMetric.pSer D lam G = MvPowerSeries.map ι.toRingHom (taylorSer D G)

def CombIota : Prop :=
  ∀ (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D) (N N' p : ℕ) [Fact p.Prime]
    (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      (∀ (x : Formalism.MainNotions.TaylorLogMetric.VC D N N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
          (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
          Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D T L L') x →
          Formalism.MainNotions.TaylorLogMetric.admitted D N N' L₁ L₁' ∧ Formalism.MainNotions.TaylorLogMetric.EqAt D p L L₁ ∧ Formalism.MainNotions.TaylorLogMetric.EqAt D p L' L₁' →
          AlgCoef D (Formalism.MainNotions.TaylorLogMetric.U D T x (e N N' L₁ L₁'))) →
      Formalism.MainNotions.TaylorLogMetric.IsComb D T e lam L L' F →
      ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (t : Fin m → Formalism.MainNotions.TaylorLogMetric.VC D N N')
        (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
        (∀ k, Formalism.MainNotions.TaylorLogMetric.IsIntP (r k)) ∧ (∀ k, Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D T L L') (t k)) ∧
        (∀ k, Formalism.MainNotions.TaylorLogMetric.admitted D N N' (L₁ k) (L₁' k) ∧ Formalism.MainNotions.TaylorLogMetric.EqAt D p L (L₁ k) ∧
          Formalism.MainNotions.TaylorLogMetric.EqAt D p L' (L₁' k)) ∧
        F = ∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) *
          MvPowerSeries.map ι.toRingHom (taylorSer D (Formalism.MainNotions.TaylorLogMetric.U D T (t k) (e N N' (L₁ k) (L₁' k))))

end Formalism.L2.KerInert
