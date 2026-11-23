import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l}

@[reducible] def resAlg (hle : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : Algebra c.F S :=
  ((algebraMap c'.F S).comp (incF c c' hle)).toAlgebra

def nabBC (hle : c.F ≤ c'.F) (nab : NabV Xo c) : NabV Xo c' :=
  fun {S} _ _ y k F α => letI := resAlg hle S; nab (y.res hle (fun _ => rfl)) k F α

def rulBC (hle : c.F ≤ c'.F) (f : Rul Xo c) : Rul Xo c' :=
  fun p y => letI := resAlg hle p.R; evR Xo c f (y.res hle (fun _ => rfl))

def covCoeff (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) : Coeff d.l₂ where
  F := c'.F
  fin := c'.fin
  conj := c'.conj
  zeta_mem := (d.hF.le.trans hle) d.c₂.zeta_mem
  le := d.c₂.le.trans (d.hF.le.trans hle)

theorem le_covCoeff (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) : d.c₂.F ≤ (covCoeff hle d).F :=
  d.hF.le.trans hle

def ddBC (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n) : DeltaDat Xo c' n where
  pd := d.pd
  I := d.I
  l₂ := d.l₂
  Xo₂ := d.Xo₂
  c₂ := covCoeff hle d
  hF := rfl
  r := d.r
  m := d.m
  nab₂ := nabBC (le_covCoeff hle d) d.nab₂
  cδ := rulBC (le_covCoeff hle d) d.cδ
  φδ := fun q => incF c c' hle (d.φδ q)

def IoOver (hle : c.F ≤ c'.F) {n : ℕ} {Ix : Type} [Fintype Ix] (lam : Ix → Formalism.BasicNotions.DomWeight n)
    (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (io' : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) : Prop :=
  ∀ (v : VVc c lam) (v' : VVc c' lam),
    (v' : Formalism.L2.DIV.Pol c'.F Ix n) = MvPolynomial.map (incF c c' hle) (v : Formalism.L2.DIV.Pol c.F Ix n) →
      io' v' = MvPolynomial.map (incF c c' hle) (io v)

end GlobalTheory.FieldBC
