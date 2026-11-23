import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def colR (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (j : Fin r) : ℝ :=
  ‖dmin X.Gm x τ j.succ / dmin X.Gm x τ j.castSucc‖

open Classical in

def letNrm {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (xR : ℝ) (k : U.Comp) (x : Frame (U.X k).Ψ r) : Ix Dw → ℝ
  | none => ∏ τ : (U.X k).Ψ, ∏ j : Fin r, colR (U.X k) x τ j ^ ((if (U.X k).p0 ≤ (j : ℕ) then 1 else -1 : ℝ) / 4)
  | some ⟨τ', i⟩ => Real.exp (Real.log (2 * Real.pi * xR) / 2) *
      (if h : relab c σ τ' ∈ (U.X k).Ψ then
        (if hi : (U.X k).p0 + (i : ℕ) < r then colR (U.X k) x ⟨_, h⟩ ⟨_, hi⟩ ^ ((1 : ℝ) / 2) else 1)
      else if h' : conjEmb (relab c σ τ') ∈ (U.X k).Ψ then
        (if hi : (i : ℕ) < (U.X k).p0 then
          colR (U.X k) x ⟨_, h'⟩ ⟨(U.X k).p0 - 1 - i, by have := (U.X k).p0_le; omega⟩ ^ (-(1 : ℝ) / 2) else 1)
      else 1)

def IsIdOrConj {σ σ' : c.F →+* ℂ} (φ : CAt σ →ₐ[c.F] CAt σ') : Prop :=
  (∀ z : CAt σ, toC (φ z) = toC z) ∨ ∀ z : CAt σ, toC (φ z) = starRingEnd ℂ (toC z)

def RdAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ))
    (q : Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ)) : Prop :=
  ∃ (y' : FrPt Xo c (CAt (goodOf c σ))) (φ : CAt σ →ₐ[c.F] CAt (goodOf c σ)),
    IsIdOrConj φ ∧ FrMap φ y y' ∧ FrBor q.2.2 ((U (goodOf c σ)).un q.1 q.2.1) y'

open Classical in

def fnDef (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (i : Ix Dw) : ℝ :=
  if h : ∃ q, RdAt U σ y q then
    cabs ((h.choose.2.2 i : (CAt (goodOf c σ))ˣ) : CAt (goodOf c σ)) *
      letNrm (U (goodOf c σ)) xR h.choose.1 h.choose.2.1.1 i
  else 1

variable (Xo c) in

def CBaseEx (h : GenFrEx Xo c) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ y : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) y

def yPDef (h : GenFrEx Xo c) (hb : CBaseEx Xo c h) (Z : Comp Xo c) (P : Om Z →+* ℂ) : FrPt Xo c (CAt (sgOf P)) :=
  (hb Z P).choose

end Formalism.L2.Pj
