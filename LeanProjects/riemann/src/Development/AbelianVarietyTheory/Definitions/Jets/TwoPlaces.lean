import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDepth

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

attribute [local instance] Over.cartesianMonoidalCategory

structure ValExt (T : CDVR) (p : ℕ) [Fact p.Prime] : Type 1 where
  C : Type
  [fld : Field C]
  [closed : IsAlgClosed C]
  [ch0 : CharZero C]
  v : Valuation C NNReal
  O : Type
  [cr : CommRing O]
  [alg : Algebra O C]
  ints : v.Integers O
  [nonunit : Fact (¬ IsUnit (p : O))]
  [cpl : IsAdicComplete (Ideal.span {(p : O)}) O]
  [loc : IsLocalRing O]
  [zp : Algebra ℤ_[p] O]
  ι : T.V →+* O
  ι_local : IsLocalHom ι
  ιF : T.Fr →+* C
  comp : ∀ x : T.V, ιF (algebraMap T.V T.Fr x) = algebraMap O C (ι x)
  val : ∀ x : T.Fr, x ≠ 0 → (v (ιF x) : ℝ) = (v (p : C) : ℝ) ^ ((vV T.V x : ℝ) / (vV T.V (p : T.Fr) : ℝ))

attribute [instance] ValExt.fld ValExt.closed ValExt.ch0 ValExt.cr ValExt.alg ValExt.nonunit ValExt.cpl ValExt.loc
  ValExt.zp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsTypes {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (io : c.F →+* T.Fr)
    (τO : (E →+* ℂ) → (𝓞 E →+* X.O)) : Prop :=
  ∀ τ a, algebraMap X.O X.C (τO τ a) = X.ιF (io (embK c τ a))

structure UnifChart [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p) : Type 1 where
  T' : CDVR
  ι' : T'.V →+* X.O
  ι'_local : IsLocalHom ι'
  t : SAB H (Sp T'.V)
  P : PELUnif (maximalIdeal T'.V) t
  F : FGLaw T'.V (chD Ch.ch)
  x : ∀ m : ℕ, algOver T'.V (JetR T'.V (Fin 1 × Fin (chD Ch.ch)) m) ⟶ t.G
  chart : IsChartJ t.G F x
  act : Germ.OAct (𝓞 E) F
  acts : ChartActs t.G x t.act.toRingAct act
  law_eq : F.mapF ι' = fun i => MvPowerSeries.map X.ι (Ch.FT i)
  act_eq : ∀ a, actMap ι' act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)

def TwoPlaces (H : Host E) (f : ℕ) (vd : ℝ) : Prop :=
  letI := H.starRing
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    v.Integers O → ∀ [Fact (¬ IsUnit ((2 : ℕ) : O))] [Algebra ℤ_[2] O] (τO : (E →+* ℂ) → (𝓞 E →+* O)),
    Function.Injective τO → (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ τO τ H.rt = τO τ' H.rt) →
    ∃ w : Place 2 (𝓞 E), w.n = f ∧ (∀ σ, σ ∈ Emb (O := O) w.e ↔ ∃ τ, InPsi H τ ∧ σ = τO τ) ∧
      (∀ σ, σ ∈ Emb (O := O) w.bar ↔ ∃ τ, ¬ InPsi H τ ∧ σ = τO τ) ∧
      ∃ t : Fin w.n ≃ Emb (O := O) w.e, HasVd 2 v w t vd

end GlobalTheory.CharDepth
