import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusMarkingPhase

open NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def normSqAt (X : FD.Data E r) (x : FD.Frame X.Ψ r) (v : Fin r → E) : ℝ :=
  ∑ τ : X.Ψ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v)

def altForm (X : FD.Data E r) (v w : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm v w)

def IsMarking (X : FD.Data E r) (x : FD.Frame X.Ψ r) (T : I2.PT E) (φ : X.Λ ≃+ T.L) : Prop :=
  (∀ (α : 𝓞 E) (v : X.Λ),
    (φ (α • v) : I2.Vsp T.dim) = I2.act α (φ v : I2.Vsp T.dim)) ∧
  (∀ v : X.Λ, ‖(φ v : I2.Vsp T.dim)‖ ^ 2 = normSqAt X x (v : Fin r → E)) ∧
  (∀ v w : X.Λ, (I2.Hf (φ v : I2.Vsp T.dim) (φ w : I2.Vsp T.dim)).im =
    (altForm X (v : Fin r → E) (w : Fin r → E) : ℝ))

def IsTorusAt (X : FD.Data E r) (x : FD.Frame X.Ψ r) (T : I2.PT E) : Prop :=
  x ∈ X.dom ∧ ∃ φ : X.Λ ≃+ T.L, IsMarking X x T φ

def phAt (X : FD.Data E r) (θ : ℝ) (x : FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < θ then 2 * (I2.PT.f E : ℝ) / (I2.PT.rd E ^ 2 * X.la1 x ^ 2) else 0

def ph (X : FD.Data E r) (q : ℕ) (R0 : ℝ) (x : FD.Frame X.Ψ r) : ℝ :=
  phAt X (I2.th (E := E) q R0) x

def TorusAtMinimum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 0 < r →
    ∀ (X : FD.Data E r) (x : FD.Frame X.Ψ r) (T : I2.PT E), IsTorusAt X x T →
      T.la1 = X.la1 x ∧ (∀ θ : ℝ, T.ph θ = phAt X θ x) ∧
        ∀ (D : ℕ) (P : I2.Par T D), P.ph = ph X P.q P.R0 x

end

end GlobalTheory.IndefiniteRowSideFullHecke.TorusMarkingPhase
