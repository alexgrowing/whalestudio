import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def BadPin (bad q1 d cond : ℕ) : Prop := 2 ∣ bad ∧ q1 ∣ bad ∧ d ∣ bad ∧ cond ∣ bad

section Reps

variable {n : ℕ} {Tup : Type} (Cl' : Tup → Type)

def RepsCov (dδ : Tup → DeltaDat Xo c n) (bad : Tup → ℕ) (Lh : ∀ t, Cl' t → Submodule (𝓞 E) (Fin n → E))
    (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ) (gam : ∀ t, Cl' t → ℕ) : Prop :=
  ∀ t, RepsOK (l := (dδ t).l₂) (bad t) (La t) (Nc t) (gam t) ∧ LatPin (Lh t) (La t)

end Reps

section Io

variable {n : ℕ} {Ix : Type} [Fintype Ix] (emb : Ix → E →+* c.F) (lam : Ix → DomWeight n)

abbrev VVc : Type := ↥(Formalism.L2.DIV.VV c.F lam)

open Classical in

def rhoM (ga : Matrix (Fin n) (Fin n) E) : VVc c lam →ₗ[c.F] VVc c lam :=
  if h : IsUnit ga.det then Formalism.L2.DIV.rhoVr emb lam (Matrix.nonsingInvUnit ga h) else 0

def nab0M : Submodule (𝓞 c.F) (VVc c lam) := Formalism.L2.DIV.nabAtr emb lam (stdLat E n)

def hwOK (hw : VVc c lam) : Prop :=
  (hw : Formalism.L2.DIV.Pol c.F Ix n) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal c.F n (lam τ)

def IoLFRec (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam) : Prop :=
  hwOK c lam hw ∧ ∃ cga : Matrix (Fin n) (Fin n) E → c.F,
    IoLF c a io (rhoM c emb lam) cga (nab0M c emb lam) hw (pG (Dw := Dw) c a n)

end Io

section Dat

variable {n : ℕ}

variable {Tup : Type} (Cl' : Tup → Type)

def WPin (dδ : Tup → DeltaDat Xo c n) (φ : ∀ t, (Fin n → LevQc Dw (dδ t).l₂) → c.F)
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) : Prop :=
  ∀ t (k : Cl' t) (q : Fin n → LevQ Dw (dδ t).l₂),
    (dδ t).eF (w t k q) = phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q

def CovPin (dδ : Tup → DeltaDat Xo c n) : Prop :=
  ∀ t, (dδ t).IsLev ∧ (dδ t).l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab (dδ t).Xo₂ (dδ t).c₂ (dδ t).nab₂

end Dat

end Formalism.L2.Pj
