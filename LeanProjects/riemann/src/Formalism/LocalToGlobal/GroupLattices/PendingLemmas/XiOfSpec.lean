import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]
  (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc)

def volE (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup) : ℤ :=
  (NN X.G.P.m X.t j : ℤ) * len X v (j + 1) L' - (NN X.G.P.m X.t (j + 1) : ℤ) * len X v j L

abbrev XiTy (v : X.Pl) (j : ℕ) : Type :=
  Aw X v j → ((Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) →+ MvPowerSeries (X.ZA j) Kc)

def IsXi (v : X.Pl) (j : ℕ) (Ξ : XiTy X Kc v j) : Prop :=
  ∃ u u' : X.G.Kf, X.vEqK u 0 ∧ X.vEqK u' 0 ∧
    ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      ThF j La La' = (u ^ (len X v j La.2) * u' ^ (len X v (j + 1) La'.2) *
        (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * volE X v j La.2 La'.2))) •
        Ξ (aw X v j La La') (X.ind v j La.2 La'.2)

def XiEx (v : X.Pl) (j : ℕ) : Prop := ∃ Ξ : XiTy X Kc v j, IsXi X Kc ThF v j Ξ

def xiOf (v : X.Pl) (j : ℕ) : XiTy X Kc v j := by
  classical exact if h : XiEx X Kc ThF v j then Classical.choose h else fun _ => 0

theorem xiOf_spec {v : X.Pl} {j : ℕ} (h : XiEx X Kc ThF v j) : IsXi X Kc ThF v j (xiOf X Kc ThF v j) := by
  rw [xiOf, dif_pos h]
  exact Classical.choose_spec h

end Formalism.L2.G.Pend
