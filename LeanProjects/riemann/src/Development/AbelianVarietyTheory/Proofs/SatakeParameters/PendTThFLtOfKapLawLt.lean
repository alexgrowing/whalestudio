import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwU

theorem pendT_ThF_lt_of_kapLawLt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; KapLawLt X ℂ_[p] (thFOf X pos F) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La') ∧ ∀ v, ∀ j < X.mm, XiEx X ℂ_[p] (thFOf X pos F) v j → XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j := by
  intro p _ X _ E hfin hst g hLT T pos F
  intro hK
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  have h1 : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La' := by
    rintro j hj ⟨c, L⟩ La' hL hL'
    change thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin (thFOf X pos F)) j (c, L) La' = _
    rw [thN_eq]
    generalize delt X hfin j c L = δ
    have hL2 : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul δ⁻¹ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ δ⁻¹ L).2 hL
    have := hK j hj c _ La' δ hL2 hL'
    rw [lsmul_lsmul_inv] at this
    exact this.symm
  refine ⟨h1, ?_⟩
  rintro v j hj ⟨Ξ, u, u', hu, hu', hΞ⟩
  refine ⟨Ξ, u, u', hu, hu', fun La La' hL hL' => ?_⟩
  rw [h1 j hj La La' hL hL']
  exact hΞ La La' hL hL'

end GlobalTheory.TwU
