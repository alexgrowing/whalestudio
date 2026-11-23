import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.AdmRed

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

namespace Formalism.L2.KerInert

def LowZC {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) (j : ℕ) (v : X.Pl) : Prop :=
  letI := wittFractionAlgebraCp p
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p], IntR (OcC p) (inParamK p ℂ_[p] U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      GeZ (MvPolynomial.coeff n (applyD (X.PIv j I v)
        (X.ThZA ℂ_[p] j (MvPowerSeries.map (algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 p) ℂ_[p])
          (expS p (-(∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
            sub2 p be (MvPowerSeries.X (Sum.inl (⟨v, e⟩ : X.EA j))) (MvPowerSeries.X (Sum.inr (⟨v, e⟩ : X.EA j)))))) * U))))

def FirstKernelLocalOfGeneral : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    RepresentativeCondition X E hfin be pos F → LocalRepresentativeCondition X E hfin be pos F

def Adm3OfK1LowerBound : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    (∀ j < X.mm, ∀ v, LowZC X be j v) → RepresentativeCondition X E hfin be pos F → Adm3Rep X E hfin pos F

end Formalism.L2.KerInert
