import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsFinExt (T T' : CDVR) (i : T.Fr →+* T'.Fr) : Prop :=
  (letI := i.toAlgebra; FiniteDimensional T.Fr T'.Fr) ∧
    ∃ r : ℕ, 0 < r ∧ ∀ x : T.Fr, vV T'.V (i x) = (r : ℤ) * vV T.V x

example (T : CDVR) : IsFinExt T T (RingHom.id _) :=
  ⟨Module.Finite.self _, 1, one_pos, fun x => by simp⟩

variable (H l) in

def IsHeckePrime (𝔓 : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M'

variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev PtClass : Type 1 := ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop

def goodCls : PtClass Xo c := fun _ _ y => GlobalTheory.GoodPts.Good y

def trivialClassCondition : PtClass Xo c := fun _ _ _ => True

variable {Xo c}

def IsIntegralUpToUnits (cls : PtClass Xo c) (T : CDVR) (io : c.F →+* T.Fr) {Ω : Type} [Field Ω] [Algebra c.F Ω]
    (k : T.Fr →+* Ω) (z : FrPt Xo c Ω) : Prop :=
  ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr), IsFinExt T T' i ∧
    letI := (i.comp io).toAlgebra
    ∃ (j : T'.Fr →ₐ[c.F] Ω), j.toRingHom.comp i = k ∧
      ∃ (y' : IntFr Xo c T' (i.comp io)), y'.IsAlg ∧ cls T' (i.comp io) y' ∧
        ∃ (w : FrPt Xo c Ω) (u : Ix Dw → T'.Vˣ), FrMap j y'.1 w ∧
          FrBor (fun a => Units.map (j.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u a)) w z

variable (Xo c)

def AtHeckePoints (cls : PtClass Xo c)
    (Q : ∀ (_ : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (_ : c.F →+* T.Fr) (Ω : Type) [Field Ω] [Algebra c.F Ω],
      (T.Fr →+* Ω) → FrPt Xo c Ω → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime H l 𝔓 p →
    (p : 𝓞 c.F) ∉ la.asIdeal →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, algCls Xo c T io y → cls T io y →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω],
      letI := io.toAlgebra
      ∀ k : T.Fr →ₐ[c.F] Ω, (letI := k.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr Ω) →
      ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ →
      ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω),
        hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → Q la T io Ω k.toRingHom z

def HeckeFrameInt (cls : PtClass Xo c) : Prop :=
  AtHeckePoints Xo c cls fun _ T io _ _ _ k z => IsIntegralUpToUnits cls T io k z

def HeckeValueInt (cls : PtClass Xo c) : Prop :=
  AtHeckePoints Xo c cls fun la T _ _ _ _ k z =>
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
        (∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
        (k.comp (algebraMap T.V T.Fr)).IsIntegralElem (evR Xo c f z)

def HeckeIntGood : Prop := HeckeFrameInt Xo c (goodCls Xo c) ∧ HeckeValueInt Xo c (goodCls Xo c)

def HeckeIntAll : Prop := HeckeFrameInt Xo c (trivialClassCondition Xo c) ∧ HeckeValueInt Xo c (trivialClassCondition Xo c)

def HeckeInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), HeckeIntGood Xo c ∧ HeckeIntAll Xo c

example (h : HeckeValueInt Xo c (trivialClassCondition Xo c)) : HeckeValueInt Xo c (goodCls Xo c) :=
  fun la P p i hP hp T io e ho y hy _ => h la P p i hP hp T io e ho y hy trivial

end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39
