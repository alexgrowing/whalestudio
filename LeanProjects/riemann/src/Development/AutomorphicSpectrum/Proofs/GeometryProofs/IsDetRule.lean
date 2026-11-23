import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FlatTie

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def RuleTie (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (t : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (z : FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c),
    under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U →
    ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
      (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
      ψ (t p z) = φ F y v w

open Classical in

def detExp (τ : E →+* ℂ) : (E →+* ℂ) × ℕ → ℕ := fun x => if x.1 = τ then 1 else 0

variable (Xo c) in

def IsDetRule (τ τ' : E →+* ℂ) (s : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) s ∧
    ∀ (p : TRing c.F) (t : Ix D → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      wchar (ex D (detExp τ') 0) t * s p y' = wchar (ex D (detExp τ) 0) t * s p y

open Classical in

def oneAt {Ψ : Finset (E →+* ℂ)} (r : ℕ) (ρ : E →+* ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r :=
  fun ρ' _ => if ρ'.1 = ρ then 1 else 0

end GlobalTheory.CompanionTheory.Ar.Rec.FlatTie
