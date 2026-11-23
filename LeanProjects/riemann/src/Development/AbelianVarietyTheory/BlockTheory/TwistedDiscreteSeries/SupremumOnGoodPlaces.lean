import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SupremumOnGoodPlaces

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Good

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def HasGoodRed (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  ∃ (𝒜 : Over (Sp T.V)) (_ : GrpObj 𝒜) (A : Over (Sp T.Fr)) (_ : GrpObj A)
    (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ Xo.univ.t.G.left),
    IsAbelianScheme 𝒜 ∧ IsGrpPullback A 𝒜 (spMap (algebraMap T.V T.Fr)) φ₁ ∧ IsGrpPullback A Xo.univ.t.G x φ₂

def goodAlg (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop :=
  letI := ι.toAlgebra
  y.IsAlg ∧ HasGoodRed Xo T y.1.x

end Good

variable {D : D7}

def GeAtGood (T : Core D) (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (b : ℝ) (f : T.R j) : Prop :=
  ∀ (W : CDVR) (ι : T.Q.c.F →+* W.Fr) (e : ℕ), OverLa la W.V ι e →
    ∀ y : IntFr (T.Q.Xo j) T.Q.c W ι, goodAlg (T.Q.Xo j) T.Q.c W ι y → (b : EReal) ≤ nval W.V e (evI y f)

def TransferAt (T : Core D) (j : ℕ) (b : ℝ) : Prop :=
  ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ T.cuspA j a n,
    ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), GeAtGood T j la b f → ∀ y : T.PtM j la, (b : EReal) ≤ y.1 f

def SupOnGood : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → TransferAt T j 0

def SupOnGoodReal : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ b : ℝ, TransferAt T j b

end GlobalTheory.IndefiniteRowSideFullHecke.SupremumOnGoodPlaces
