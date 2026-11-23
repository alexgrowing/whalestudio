import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SubstZOfXCoordZA
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.XiOfSpec
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetYtMatNeZero

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

@[reducible] def wittFractionAlgebraCp (p : ℕ) [Fact p.Prime] : Algebra (K0 p) ℂ_[p] := (k0ToC p).toAlgebra

@[reducible] def algKfC {G : GAtP p} (E : CEmb G) : Algebra G.Kf ℂ_[p] := E.iK.toAlgebra

abbrev DelTy (X : Sys p) (E : CEmb X.G) : Type :=
  letI := algKfC E
  ∀ j, (X.Pj j).Xsp →ₗ[X.G.Kf] MvPowerSeries (X.ZA j) ℂ_[p] →ₗ[X.G.Kf] XspC (X.Pj (j + 1)) ℂ_[p]

def DelDeg (X : Sys p) (E : CEmb X.G) (DelF : DelTy X E) : Prop :=
  letI := algKfC E
  ∀ j (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) ℂ_[p]),
    (∀ n : X.ZA j →₀ ℕ, (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
        ((∑ a, ∑ b, n ⟨v, (s, a, b)⟩ : ℕ) : ℤ) = ∑ i ∈ Finset.Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i) →
      MvPowerSeries.coeff n f = 0) → DelF j G f = 0

abbrev pendOf (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p])
    (DelF : DelTy X E) (hDel : DelDeg X E DelF) : Pend X :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  { Kc := ℂ_[p]
    Oc := OcC p
    Oc_val := OcC_val
    witt_mem_integers_Cp := fun x => by
      show ‖k0ToC p (algebraMap (WW p) (K0 p) x)‖ ≤ 1
      rw [witt_fraction_to_Cp_algebraMap]
      exact norm_wToC_le p x
    Oc_K := fun x => E.mem_iff x
    Oc_rank1 := OcC_rank1
    be := be
    Rep := repOf X.Lv hfin
    Rep_lat := repOf_lat X.Lv hfin
    Rep_ex := fun j _ => repOf_ex X.Lv hfin j
    stab_fin := fun j _ => stab_fin X hst j
    Frm := Frm X
    ThA := fun j La La' φ => thA ℂ_[p] φ (ThF j La La')
    bc := fun _ _ _ φ => bc ℂ_[p] φ
    ThF := ThF
    ThF_frm := fun j La La' φ => thF_frm ℂ_[p] φ (ThF j La La')
    DelF := DelF
    Del_deg := hDel
    len := len X
    len_edge := len_edge X
    len_other := len_other X
    Aw := Aw X
    aw := aw X
    weight_update_at_place := weight_update_at_place X
    aw_tgt := aw_tgt X
    Xi := xiOf X ℂ_[p] ThF }

abbrev pendC (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Pend X :=
  letI := algKfC E
  pendOf X E hfin hst be ThF (delF X ℂ_[p]) (del_deg X ℂ_[p])

end Formalism.L2.G.Pend
