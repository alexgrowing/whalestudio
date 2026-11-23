import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open Formalism.MainNotions.DIV.Cons (intO)
open Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam MonObj Limits GlobalTheory.HalfGeo GlobalTheory.EqHalf
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def DlogVals {p : ℕ} [Fact p.Prime] (xO : Sp ↥(intO ℂ_[p]) ⟶ X) {n N g : ℕ} (χ : Fin N → TorsChar t xO (p ^ n))
    (u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (Mc : Matrix (Fin N) (Fin g) ℂ_[p]) : Prop :=
  ∀ (vO : Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left) (cf : Fin g → ℂ_[p]), IsTanAtG t xO vO →
    IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ xO) u cf (spMap (dualMap (intO ℂ_[p]).subtype) ≫ vO) →
    ∀ m, ∃ r : ↥(intO ℂ_[p]), (r : ℂ_[p]) = ∑ l, Mc m l * cf l ∧
      ∀ w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) (DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}))) ≫ xO) ⟶ t.G,
        w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}))) ≫ vO →
          ((χ m).χ _ w : DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ n})).snd =
            Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) r

def Equivar {O : Type} [CommRing O] {x : Sp O ⟶ X} {q N : ℕ} (χ : Fin N → TorsChar t x q)
    (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) : Prop :=
  ∀ (α : 𝓞 E) (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
    (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G), w ^ q = 1 →
      ∀ m, (χ m).χ B (w ≫ t.act.act α) = ∏ m', (χ m').χ B w ^ ρ α m m'

end Gen

section Setup

variable {D : D7} (O : Setup D) (c : O.s.Comp)

theorem length_letters : (letters O.S.Dw).length = D.R.f * O.N :=
  (GlobalTheory.Proof.LetterConjugation.letters_spec D O.A O.N O.j O.S O.κ O.s).1

def letterAt (l : Fin (D.R.f * O.N)) : Letter O.S.Dw := (letters O.S.Dw).get (Fin.cast (length_letters O).symm l)

def frAt (y : (O.Φ.C c).Y.X) :=
  ((O.Φ.C c).gr_spec y).choose_spec.choose

def dgOf (y : (O.Φ.C c).Y.X) (l : Fin (D.R.f * O.N)) : (O.Φ.C c).Y.Fnˣ :=
  ((O.Φ.C c).gr_spec y).choose_spec.choose_spec.choose (letterAt O l).1 (letterAt O l).2

variable {v : HeightOneSpectrum (𝓞 D.what₂.LL)} [Fact (resP v).Prime] (e : Ext v) (y : AlgPt (O.Φ.C c).Y)

def psiAt : (O.Φ.C c).Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] :=
  (ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom

def ptAt : Sp ℂ_[resP v] ⟶ O.s.T.Z.X :=
  spMap (psiAt O c e y) ≫ stalkPt (O.Φ.C c).Y (below y.1) ≫ (O.Φ.C c).π ≫ genι O.s.T.Z

def uAt (l : Fin (D.R.f * O.N)) : Sp (DualNumber ℂ_[resP v]) ⟶ O.s.T.Z.t.G.left :=
  spMap (dualMap (psiAt O c e y)) ≫ (frAt O c (below y.1)).v (letterAt O l).1 (letterAt O l).2

def WeilData {n : ℕ} (xO : Sp ↥(intO ℂ_[resP v]) ⟶ O.s.T.Z.X)
    (χ : Fin (D.R.f * O.N + D.R.f * O.N) → TorsChar O.s.T.Z.t xO (resP v ^ n))
    (B : Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ) : Prop :=
  ∃ (yy : Sp ℂ_[resP v] ⟶ O.s.Xo.XF O.κ.c) (s : Fin (D.R.f * O.N + D.R.f * O.N) → (Over.mk yy ⟶ O.s.T.Z.oF.t.G))
    (ζ : ℂ_[resP v]ˣ), IsPrimitiveRoot ζ (resP v ^ n) ∧ HasPoint O.s.T.Z.oF.t O.s.T.Z.m.φ xO yy ∧
    IsGram O.s.T.Z.oF.t (resP v ^ n) s ζ B ∧ ∀ m, IsWeilChar O.s.T.Z.oF.t O.s.T.Z.m.φ (s m) (χ m)

def PtData (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ)
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) {Ch : Type}
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)) :
    Prop :=
  haveI : Fact (resP v).Prime := ⟨hp⟩
  ∃ (xO : Sp ↥(intO ℂ_[resP v]) ⟶ O.s.T.Z.X)
    (χ : Fin (D.R.f * O.N + D.R.f * O.N) → TorsChar O.s.T.Z.t xO (resP v ^ n)),
    spMap (intO ℂ_[resP v]).subtype ≫ xO = ptAt O c e y ∧ Gens χ ∧ WeilData O xO χ (gram O.S.Dw b) ∧
      Equivar O.s.T.Z.t χ (chiAct O.S.Dw b) ∧
      ∀ a, inC a → DlogVals O.s.T.Z.t xO χ (uAt O c e y) ((M a).map (ioOf (resP v) e))

abbrev wholeA (P : Finset ℕ) (R : ℝ) (i : Fin (D.R.f * O.N)) : Adl (cxSt D.what₂.LL) (O.Φ.C c).Y :=
  adlOf (O.Φ.C c) (O.met.hm c) (wholeSym (ArIn.ind P) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))

abbrev eigA (P : Finset ℕ) (R : ℝ) (i : Fin (D.R.f * O.N)) : Adl (cxSt D.what₂.LL) (O.Φ.C c).Y :=
  adlOf (O.Φ.C c) (O.met.hm c) (eigSym O.S.Dw (ArIn.ind P) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))

end Setup

end GlobalTheory.EqHalf
