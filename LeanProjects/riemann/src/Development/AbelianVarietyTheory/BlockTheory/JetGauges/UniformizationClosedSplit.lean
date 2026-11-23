import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def PrimeToLevel (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ((l.M' : ℕ) : 𝓞 c.F) ∉ la.asIdeal

def HasModel (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
    (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ Y.N3

def ClosedSplit (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj G.G)

def HasUnif (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) G, P.TorsionIso

variable (Xo : Moduli Dw l) (c : Coeff l)

def ModelAt : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModel Xo c T io

def UnifOfModel : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), HasModel Xo c T io →
    ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

def UnifAt : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

variable {Xo c}

theorem unifAt_of (h₁ : ModelAt Xo c) (h₂ : UnifOfModel Xo c) : UnifAt Xo c :=
  fun la hla T io e ho => h₂ T io (h₁ la hla T io e ho)

example {O : Type} [CommRing O] (T : CDVR) (b : O →+* T.V) (n : ℕ) (hn : ¬ IsUnit (n : T.V)) : ¬ IsUnit (n : O) :=
  fun h => hn (by simpa using h.map b)

theorem PrimeToLevel.not_mem_M {la : HeightOneSpectrum (𝓞 c.F)} (h : PrimeToLevel c la) :
    ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal := by
  intro hM
  apply h
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hM

end General

def Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c ∧ UnifOfModel Xo c

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
