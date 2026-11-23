import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoefficientFieldBaseChange

noncomputable section

namespace GlobalTheory.ModuliCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Tor.Host E}

theorem dim_eq (D : Tor.Datum H) : D.dim = IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.dimD D := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h
  unfold Tor.Datum.dim IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.dimD
  rw [← h, Nat.mul_div_cancel _ two_pos]

variable {D : Tor.Datum H} {l : Tor.Level H}

theorem isModuli_of_moduli (Xo : Tor.Moduli D l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l Xo.s Xo.univ where
  smooth := dim_eq D ▸ Xo.smooth
  qproj := Xo.qproj
  repr S hS s o := Xo.rep S s hS o
  rigid := Xo.unram

def moduliOfIsModuli {X : Scheme.{0}} {str : X ⟶ Tor.Sp (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.KA l)}
    {univ : Tor.Obj D l (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseKA l) str} (h : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l str univ) : Tor.Moduli D l where
  X := X
  s := str
  qproj := h.qproj
  smooth := (dim_eq D).symm ▸ h.smooth
  univ := univ
  rep S s hS o := @IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli.repr _ _ _ _ _ _ _ _ _ _ h S hS s o
  unram := h.rigid

def moduliEquiv (D : Tor.Datum H) (l : Tor.Level H) :
    Tor.Moduli D l ≃
      {p : Σ (X : Scheme.{0}) (str : X ⟶ Tor.Sp (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.KA l)), Tor.Obj D l (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseKA l) str //
        IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l p.2.1 p.2.2} where
  toFun Xo := ⟨⟨Xo.X, Xo.s, Xo.univ⟩, isModuli_of_moduli Xo⟩
  invFun p := moduliOfIsModuli p.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem isCoeffField_of_coeff (c : Tor.Coeff l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l c.F where
  fin := c.fin
  conj := c.conj
  root := c.zeta_mem

def coeffOfIsCoeffField {F₀ : IntermediateField ℚ ℂ} (h : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l F₀) : Tor.Coeff l where
  F := F₀
  fin := h.fin
  conj := h.conj
  zeta_mem := h.root
  le := h.KA_le

def coeffEquiv (l : Tor.Level H) : Tor.Coeff l ≃ {F₀ : IntermediateField ℚ ℂ // IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l F₀} where
  toFun c := ⟨c.F, isCoeffField_of_coeff c⟩
  invFun F := coeffOfIsCoeffField F.2
  left_inv _ := rfl
  right_inv _ := rfl

end GlobalTheory.ModuliCompare
