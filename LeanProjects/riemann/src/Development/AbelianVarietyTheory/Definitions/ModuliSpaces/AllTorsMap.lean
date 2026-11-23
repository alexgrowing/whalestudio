import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatTors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Generic

variable {R : Type} [CommRing R] [IsDomain R]

abbrev genPart (T : Over (Sp R)) : Over (Sp R) := Over.mk (pullback.fst T.hom (jK R) ≫ T.hom)

def genι (T : Over (Sp R)) : genPart T ⟶ T := Over.homMk (pullback.fst T.hom (jK R)) rfl

def FinFlatEt {W : (Sp R).Opens} (T : Over W.toScheme) : Prop :=
  IsFinite T.hom ∧ Flat T.hom ∧ Etale (pullback.snd (overW W T).hom (jK R))

def OverGen (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over (Sp R)) (x : Sp F ⟶ T.left) : Prop :=
  x ≫ T.hom = jFK (R := R) F ≫ jK R

def PairRep {D : DegPre R} {W : (Sp R).Opens} (ψW : PsiOn D W) (k : ℕ) (y : D.X) (N : Over W.toScheme)
    (p₀ : QkPtW D W ψW k N) : Prop :=
  FinFlatEt N ∧ Surjective N.hom ∧ p₀.y = y ∧
    ∀ (T : Over W.toScheme) (p : QkPtW D W ψW k T), p.y = y → ∃! h : T ⟶ N, QkPtW.IsPull h p₀ p

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

def IsImage (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (q : QkPt P.D.toPre F k)
    (v : Sp F ⟶ t.G.left) : Prop :=
  ∃ a : TFK (R := R) F ⟶ P.A.A, a.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = v ∧ P.ToA F k q a

def IsTorsMap (P : PELUnif I t) {W : (Sp R).Opens} (ψW : PsiOn P.D.toPre W) (k : ℕ)
    (f : ∀ T : Over W.toScheme, QkPtW P.D.toPre W ψW k T → (overW W T ⟶ t.G)) : Prop :=
  (∀ T p, f T p ^ k = 1) ∧
  (∀ (T T' : Over W.toScheme) (h : T' ⟶ T) p p', QkPtW.IsPull h p p' → f T' p' = (Over.map W.ι).map h ≫ f T p) ∧
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (T : Over W.toScheme) (x : Sp F ⟶ T.left),
    OverGen F (overW W T) x → ∀ p (q : QkPt P.D.toPre F k), QkPtW.IsPullF F x p q → IsImage P F k q (x ≫ (f T p).left)

def AllFlat (p : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) {W : (Sp R).Opens},
    PsiOn P.D.toPre W → ℕ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CharZero R], AdmBase R (maximalIdeal R) → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : (Sp R).Opens),
    (W : Set (Sp R)).Nonempty → IsProper (t.G.hom ∣_ W) → ∀ (ψW : PsiOn P.D.toPre W) (k : ℕ), 1 ≤ k → p P ψW k

def AllTorsMap (p : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) {W : (Sp R).Opens}
    (ψW : PsiOn P.D.toPre W) (k : ℕ),
    (∀ T : Over W.toScheme, QkPtW P.D.toPre W ψW k T → (overW W T ⟶ t.G)) → Prop) : Prop :=
  AllFlat fun P _ ψW k => ∀ f, IsTorsMap P ψW k f → p P ψW k f

def JointFull : Prop :=
  N0 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l,
      ∃ Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W,
        (∀ p W hp hW, N2 (Y p W hp hW) ∧ ∀ i, (Y p W hp hW i).SplitFibres ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.ModelFull (Y p W hp hW i) ∧
          (Y p W hp hW i).N4) ∧ N6 Y

end GlobalTheory.FlatTors
