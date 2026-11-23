import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FlatDeterminantSections

open Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable (D : D7) (i : Fin D.R.m)

abbrev pJ : ℕ := (D.R.sigW ((i : ℕ) + 1)).1

abbrev qJ : ℕ := (D.R.sigW ((i : ℕ) + 1)).2
end

section Flat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} (T : Core D)

open Classical in

def detA (τ : D.host.E →+* ℂ) : (D.host.E →+* ℂ) × ℕ → ℕ := fun x => if x.1 = τ then 1 else 0

def IsDetSec (j : ℕ) (τ τ' : D.host.E →+* ℂ) (s : T.R j) : Prop :=
  IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) s ∧
    ∀ (p : TRing T.Q.c.F) (t : Ix (T.Q.Dw j) → (p.R)ˣ) (y y' : FrPt (T.Q.Xo j) T.Q.c p.R), FrBor t y y' →
      wchar (ex (T.Q.Dw j) (detA τ') 0) t * s p y' = wchar (ex (T.Q.Dw j) (detA τ) 0) t * s p y

def IsFlatGen (j : ℕ) (τ : D.what₂.Tau) (s : T.R j) : Prop :=
  IsDetSec T j (DV.tauEmb D τ) (conjEmb (DV.tauEmb D τ)) s ∧
    ∃ s' : T.R j, IsDetSec T j (conjEmb (DV.tauEmb D τ)) (DV.tauEmb D τ) s' ∧ s * s' ≠ 0 ∧ s * (s * s') = s ∧
      ∀ f ∈ sec (T.Q.Xo j) T.Q.c 0 0, ∃ a : T.Q.c.F, f * (s * s') = a • (s * s')

def FlatEx : Prop := ∀ (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ s, IsFlatGen T ((i : ℕ) + 1) τ s

def finN (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (s : T.R j) : ℝ := ⨆ y : T.PtM j la, T.nrmM j la y s

open Classical in

def laFlat (j : ℕ) (σ : T.Q.c.F →+* ℂ) (τ : D.host.E →+* ℂ) (k : (T.U j σ).Comp) : Wt ((T.U j σ).X k).Ψ D.R.r :=
  fun ρ _ => if ρ.1 = relab T.Q.c σ τ then 1 else 0

def infN (j : ℕ) (τ : D.what₂.Tau) (σ : T.Q.c.F →+* ℂ) (s : T.R j) : ℝ :=
  lieFac (T.Q.Dw j) (xiR D) (detA (DV.tauEmb D τ)) / lieFac (T.Q.Dw j) (xiR D) (detA (conjEmb (DV.tauEmb D τ))) *
    supN (T.U j (goodOf T.Q.c σ)).X (laFlat T j (goodOf T.Q.c σ) (DV.tauEmb D τ)) (rdU (T.U j (goodOf T.Q.c σ)) s)

def degFr (j : ℕ) (τ : D.what₂.Tau) (s : T.R j) : ℝ :=
  -((∑ᶠ la, Real.log (finN T j la s)) + ∑ σ : T.Q.c.F →+* ℂ, Real.log (infN T j τ σ s)) / (finrank ℚ T.Q.c.F : ℝ)

variable (D) in

def vd (l : ℕ) : ℝ := ((discr D.host.E).natAbs.factorization l : ℝ) / (finrank ℚ D.host.E : ℝ)

variable (D) in

def flDefect (i : Fin D.R.m) : ℝ :=
  (qJ D i : ℝ) * (vd D 2 * Real.log 2 + vd D D.host.q * Real.log D.host.q - vd D D.host.d * Real.log D.host.d)

def flatGen (hF : FlatEx T) (i : Fin D.R.m) (τ : D.what₂.Tau) : T.R ((i : ℕ) + 1) := (hF i τ).choose

def c1W (hF : FlatEx T) (i : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  degFr T ((i : ℕ) + 1) τ (flatGen T hF i τ) + flDefect D i

def FlatDegIndep : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau) (s s' : T.R ((i : ℕ) + 1)), IsFlatGen T ((i : ℕ) + 1) τ s → IsFlatGen T ((i : ℕ) + 1) τ s' →
    degFr T ((i : ℕ) + 1) τ s = degFr T ((i : ℕ) + 1) τ s'

end Flat

end GlobalTheory.CompanionTheory.Ar.Rec.FlatDeterminantSections
