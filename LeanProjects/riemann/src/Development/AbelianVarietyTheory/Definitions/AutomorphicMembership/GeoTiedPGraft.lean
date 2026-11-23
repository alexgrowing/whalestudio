import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField

namespace GlobalTheory.GeoGraft

variable {D : D7}

def graft (Xg X₀ : DivX D) (iM : ∀ j (c : Xg.Comp j), (X₀.MjH j).V →ₗ[D.what₂.LL] Xg.geo.Fn (Xg.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xg.geo.H0 (Xg.Yv j c) (Xg.Lw j c (DV.kapW D j))) : DivX D :=
  { Xg with
    MjH := X₀.MjH, MjH_good := X₀.MjH_good, jM := X₀.jM, jM_basis := X₀.jM_basis, jM_lat := X₀.jM_lat
    MjLat_sub := X₀.MjLat_sub, jM_metric := X₀.jM_metric
    Qp := X₀.Qp, degreeZero_partial_set_empty := X₀.degreeZero_partial_set_empty, Qp_muAt := X₀.Qp_muAt, Qp_g := X₀.Qp_g
    QPl := X₀.QPl, finQ := X₀.finQ, qv := X₀.qv, qv_gt := X₀.qv_gt, qv_char := X₀.qv_char
    nu := X₀.nu, nu_ne := X₀.nu_ne, nu_abs := X₀.nu_abs, ZQ := X₀.ZQ, quotientLocalValueFirst := X₀.quotientLocalValueFirst, typeDim := X₀.typeDim
    iMj := iM, iMj_mem := hiM
    logLam := X₀.logLam, logLam_base := X₀.logLam_base
    kapR := X₀.kapR, kapR_pos := X₀.kapR_pos, kapR_conj := X₀.kapR_conj }

def Keeps (X X₀ : DivX D) : Prop := ∃ Xg iM hiM, X = graft Xg X₀ iM hiM

theorem Keeps.refl (X : DivX D) : Keeps X X := ⟨X, X.iMj, X.iMj_mem, rfl⟩

theorem Keeps.trans {X Y Z : DivX D} (h : Keeps X Y) (h' : Keeps Y Z) : Keeps X Z := by
  obtain ⟨Zg, i, hi, rfl⟩ := h'
  obtain ⟨Yg, i', hi', rfl⟩ := h
  exact ⟨Yg, i', hi', rfl⟩

theorem Keeps.symm {X Y : DivX D} (h : Keeps X Y) : Keeps Y X := by
  obtain ⟨Yg, i', hi', rfl⟩ := h
  exact ⟨Y, Y.iMj, Y.iMj_mem, rfl⟩

theorem Keeps.mjH {X X₀ : DivX D} (h : Keeps X X₀) : X.MjH = X₀.MjH ∧ HEq X.jM X₀.jM := by
  obtain ⟨_, _, _, rfl⟩ := h; exact ⟨rfl, HEq.rfl⟩

theorem Keeps.num {X X₀ : DivX D} (h : Keeps X X₀) :
    X.kapR = X₀.kapR ∧ X.logLam = X₀.logLam ∧ X.Qp = X₀.Qp ∧ X.QPl = X₀.QPl ∧ HEq X.qv X₀.qv ∧ HEq X.nu X₀.nu ∧
      HEq X.ZQ X₀.ZQ ∧ HEq X.quotientLocalValueFirst X₀.quotientLocalValueFirst ∧ HEq X.typeDim X₀.typeDim := by
  obtain ⟨_, _, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

def GeoOver (Q : DivX D → Prop) (X₀ : DivX D) : Prop :=
  ∃ (X : DivX D) (inK : X.Lev → ℕ → Prop), Keeps X X₀ ∧ GeoTiedP X inK ∧ Q X

theorem GeoOver.mono {Q Q' : DivX D → Prop} (h : ∀ X, Q X → Q' X) {X₀ : DivX D} (g : GeoOver Q X₀) : GeoOver Q' X₀ :=
  let ⟨X, k, a, b, c⟩ := g; ⟨X, k, a, b, h X c⟩

end GlobalTheory.GeoGraft
