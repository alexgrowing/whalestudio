import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsEigenLatticeBasis (Dw : Datum H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V))
    (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) : Prop :=
  (∀ i, IsTan (ub i)) ∧ (∀ i, IsEigV c io G τ (ub i)) ∧
    ∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w

def IsEigenBasisAt (Xo : Moduli Dw l) (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X)
    (τ : E →+* ℂ) (u : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) : Prop :=
  (∀ i, IsTanAt x (u i)) ∧ (∀ i, IsEigAt c τ (u i)) ∧
    ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x u a w

def IsGenericFibre {Xo : Moduli Dw l} {T : CDVR} {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X}
    (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (w : epsOver T.V T.V ⟶ G.G) (v : Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m₁.φ = v ∧
    u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ w.left

def IntegralUpToTriangular (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (yt : Sp T.V ⟶ Y.X) (yF : Sp T.Fr ⟶ Xo.XF c),
      yF ≫ pullback.snd _ _ = spMap io → spMap (algebraMap T.V T.Fr) ≫ yt = yF ≫ Y.j →
      letI := io.toAlgebra
      ∀ y : FrPt Xo c T.Fr, y.x = yF ≫ pullback.fst _ _ →
        ∃ (y₀ : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀.1 y

def EigenLatticesFree (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = sOf c T.Fr →
    ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (τ : E →+* ℂ),
      (∃ ub, IsEigenLatticeBasis Dw c T io G τ ub) ∧
      ∀ u, IsEigenBasisAt Xo c x τ u →
        ∃ (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
          (v : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
          IsEigenLatticeBasis Dw c T io G τ ub ∧ (∀ i, IsGenericFibre m₁ m₂ (ub i) (v i)) ∧
          ∀ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x v cf (u i)

def FieldPointsFromTest (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

def IntegralFramesAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  IntegralUpToTriangular Xo c ∧ EigenLatticesFree Xo c ∧ FieldPointsFromTest Xo c

def IntegralFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), IntegralFramesAt Xo c

theorem isEigenBasisAt_frPt {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) : IsEigenBasisAt Xo c y.x τ (y.u τ) :=
  ⟨y.tan τ, y.eig τ, y.basis τ⟩

theorem exists_basis_of_integral {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (h : Integral T io y) :
    letI := io.toAlgebra
    ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t y.x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∀ τ, ∃ ub, IsEigenLatticeBasis Dw c T io G τ ub ∧
        ∀ i, IsGenericFibre m₁ m₂ (ub i) (y.u τ i) := by
  obtain ⟨G, t', m₁, m₂, ⟨ub, h1, h2, h3, h4⟩, -⟩ := h
  exact ⟨G, t', m₁, m₂, fun τ => ⟨ub τ, ⟨h1 τ, h2 τ, h3 τ⟩, h4 τ⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
