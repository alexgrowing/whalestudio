import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt

noncomputable section

namespace GlobalTheory.ArcCM

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)]

def AbDat (A : AnArc (𝓞 E)) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) : Prop :=
  (∀ a z i, A.F a z i = tyB i (a : E) * z i) ∧ IsTypeFn H DB.p DB.q tyB ∧
    (∀ (a : 𝓞 E) x, eB (a • x) = A.FLam a (eB x)) ∧ (∀ x x', DB.EF x x' = A.Ef (eB x) (eB x')) ∧
    IsPeriod DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)

def PrimAn (A : AnArc (𝓞 E)) : Prop :=
  (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam H.w0 l) l) ∧ ∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (H.w0 • x))

omit [IsCMField E] [NumberField E] in

def NormAn (A : AnArc (𝓞 E)) (n : ℕ) : Prop :=
  (∀ y, n • A.ct y ∈ A.abelian₂) ∧
    ∀ y y', eTwoPi (A.T (n • y) (n • y')) * Complex.exp (Real.pi * A.H (n • A.ct y) (n • A.ct y')) = 1

end GlobalTheory.ArcCM
