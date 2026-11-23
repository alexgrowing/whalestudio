import Formalism.LocalToGlobal.InertKernelTheory.StatementIota

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def blkPt (D : D7) {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (I : Fin n') (J : Fin n) (z : VC D N N') : VC D m m' :=
  fun τ u v => z τ (eR.symm (I, u)) (eC.symm (J, v))

def blkIdx (D : D7) {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (I : Fin n') (J : Fin n) (k : D.what₂.Tau × Fin m' × Fin m) : D.what₂.Tau × Fin N' × Fin N :=
  (k.1, eR.symm (I, k.2.1), eC.symm (J, k.2.2))

def TaylorProductOverBlocks : Prop :=
  ∀ (D : D7) (N N' n n' m m' : ℕ) (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
    (G : Fin n' → Fin n → VC D m m' → ℂ), (∀ I J, AnalyticOnNhd ℂ (G I J) Set.univ) →
    taylorSer D (fun z => ∏ I, ∏ J, G I J (blkPt D eR eC I J z)) =
      ∏ I, ∏ J, MvPowerSeries.rename (blkIdx D eR eC I J) (taylorSer D (G I J))

end Formalism.L2.KerInert
