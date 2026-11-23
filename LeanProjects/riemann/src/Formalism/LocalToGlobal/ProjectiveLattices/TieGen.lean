import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def PtIs (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Z : Comp Xo c)
    (y : FrPt Xo c (CAt σ)) (P : Om Z →+* ℂ) : Prop :=
  ∃ (φ : CAt (sgOf P) →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    (∀ z, toC (φ z) = toC z) ∧ FrMap φ (yP Z P) y' ∧ FrBor t y y'

def genU (U : Unf Xo c σ r) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (k : U.Comp)
    (Z : Comp Xo c) : Set (Frame (U.X k).Ψ r) :=
  {x | ∃ P ∈ PT (Ω := Om Z) σ, ∃ hx : x ∈ (U.X k).dom, PtIs yP Z (U.un k ⟨x, hx⟩) P}

open Classical in

def ptU (U : Unf Xo c σ r) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (k : U.Comp)
    (Z : Comp Xo c) (hne : Nonempty (Om Z →+* ℂ)) (x : Frame (U.X k).Ψ r) : Om Z →+* ℂ :=
  if h : x ∈ genU U yP k Z then h.choose else hne.some

section

variable (U : Unf Xo c σ r) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (k : U.Comp)
  (Z : Comp Xo c) (hne : Nonempty (Om Z →+* ℂ))

end

end Formalism.L2.Pj
