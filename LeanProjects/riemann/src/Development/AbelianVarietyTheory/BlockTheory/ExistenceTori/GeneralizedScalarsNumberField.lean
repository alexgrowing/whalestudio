import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralizedScalarsNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Relations

variable {Xo : Moduli Dw l} {c : Coeff l}

def GenScal {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ h : y'.x = y.x, ∀ i, (h ▸ y'.s : LB.Sec (PPx y.x)).f i = scal y.x a i * y.s.f i

def LieChange {S : Type} [CommRing S] [Algebra c.F S] (τ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) : Prop :=
  ∀ i, IsCombAt y.x (y.u τ) (fun j => M i j) (y'.u τ i)

end Relations

section Claims

variable (Xo : Moduli Dw l) (c : Coeff l)

def BaseChangeField : Prop :=
  ∀ (S T : Type) [Field S] [Algebra c.F S] [Field T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z

def ReframeIntegral : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → y'.x = y.x →
      ∃ (t : Ix Dw → T.Frˣ) (z : FrPt Xo c T.Fr), FrBor t y' z ∧ Integral T io z

def ReframeIntFr : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    letI := io.toAlgebra
    ∀ y' : FrPt Xo c T.Fr, y'.x = y.1.x →
      ∃ (t : Ix Dw → T.Frˣ) (z : IntFr Xo c T io), FrBor t y' z.1

def PointNumberField : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧
    ∃ x : Sp L ⟶ Xo.X, x ≫ Xo.s = sOf c L

def FramedPointNumberField : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧ Nonempty (FrPt Xo c L)

def CombLinearAt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (m : ℕ)
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), (∀ i, IsTanAt x (v i)) →
    (∀ cf : Fin m → S, ∃! w, IsCombAt x v cf w) ∧
    (∀ (cf : Fin m → S) w, IsCombAt x v cf w → IsTanAt x w) ∧
    (∀ τ : E →+* ℂ, (∀ i, IsEigAt c τ (v i)) → ∀ (cf : Fin m → S) w, IsCombAt x v cf w → IsEigAt c τ w) ∧
    (∀ i, IsCombAt x v (Pi.single i 1) (v i)) ∧
    ∀ (n : ℕ) (M : Fin n → Fin m → S) (w : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)),
      (∀ j, IsCombAt x v (M j) (w j)) →
      ∀ (b : Fin n → S) z, IsCombAt x w b z → IsCombAt x v (fun i => ∑ j, b j * M j i) z

def GenRatio : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), y'.x = y.x →
    (∃! a : S, GenScal a y y') ∧ ∀ a : S, GenScal a y y' → IsUnit a

def IntLieGL : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → Integral T io y' → y'.x = y.x →
      ∀ τ : E →+* ℂ, ∃ M : GL (Fin (Dw.mult τ)) T.V,
        LieChange τ ((M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V).map (algebraMap T.V T.Fr)) y y'

def IntGenUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ y y' : FrPt Xo c T.Fr, Integral T io y → Integral T io y' → y'.x = y.x →
      ∃ a : T.Vˣ, GenScal (algebraMap T.V T.Fr (a : T.V)) y y'

def IntFrameGL : Prop := IntLieGL Xo c ∧ IntGenUnit Xo c

end Claims

def CombLinear : Prop :=
  ∀ (V R : Type) [CommRing V] [CommRing R] [Algebra V R] (G : Over (Sp V)) [GrpObj G] (m : ℕ)
    (v : Fin m → (epsOver V R ⟶ G)), (∀ i, IsTan (v i)) →
    (∀ cf : Fin m → R, ∃! w, IsComb v cf w) ∧
    (∀ (cf : Fin m → R) w, IsComb v cf w → IsTan w) ∧
    (∀ i, IsComb v (Pi.single i 1) (v i)) ∧
    ∀ (n : ℕ) (M : Fin n → Fin m → R) (w : Fin n → (epsOver V R ⟶ G)), (∀ j, IsComb v (M j) (w j)) →
      ∀ (b : Fin n → R) z, IsComb w b z → IsComb v (fun i => ∑ j, b j * M j i) z

def Claims (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  BaseChangeField Xo c ∧ ReframeIntegral Xo c ∧ ReframeIntFr Xo c ∧ PointNumberField Xo c ∧
    FramedPointNumberField Xo c ∧ CombLinearAt Xo c ∧ CombLinear ∧ GenRatio Xo c ∧ IntFrameGL Xo c

section Basic₂

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem pointNumberField_of_framed (h : FramedPointNumberField Xo c) : PointNumberField Xo c := by
  obtain ⟨L, _, _, hL, ⟨y⟩⟩ := h
  exact ⟨L, inferInstance, inferInstance, hL, y.x, y.x_over⟩

theorem genScal_existsUnique {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (h : y'.x = y.x) :
    ∃! a : S, GenScal a y y' := by
  obtain ⟨a, ha, hu⟩ := y.gen (h ▸ y'.s)
  exact ⟨a, ⟨h, ha⟩, fun b ⟨_, hb⟩ => hu b hb⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralizedScalarsNumberField
