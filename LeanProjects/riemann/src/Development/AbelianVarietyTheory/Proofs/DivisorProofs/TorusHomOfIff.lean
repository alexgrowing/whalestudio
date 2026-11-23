import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.Mum.Two

def TorusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : Prop :=
  ∀ χ : X', res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
    (pullU t.left ⊤ (charUnit S X' χ)) = charUnit S X (h χ)

variable {R : Type} [CommRing R] [IsDomain R]

instance nonempty_av {S : Type} [CommRing S] [IsDomain S] (P : PolAV (Sp S)) : Nonempty P.A.left :=
  ⟨eSec P.A (⊥ : PrimeSpectrum S)⟩

abbrev JN (D₁ D₂ : DegPre R) : LB (D₁.P.A.left ⨿ D₂.P.A.left) := join D₁.P.L D₂.P.L

theorem jn_isLB (D₁ D₂ : DegPre R) : (JN D₁ D₂).IsLB := join_isLB D₁.P.isLB D₂.P.isLB

abbrev CmpLB (D₁ D₂ : DegPre R) (a : D₁.P.A ⟶ D₂.P.A) (χ₁ : D₁.X) (χ₂ : D₂.X) : LB D₁.P.A.left :=
  LB.LinComb (JN D₁ D₂) (Sum.elim (fun k => D₁.Oφ (𝟙 _) χ₁ k ≫ coprod.inl) (fun k => D₂.Oφ a χ₂ k ≫ coprod.inr))
    (Sum.elim Oε Oinvε)

def Nrm {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {χ₁ : D₁.X} {χ₂ : D₂.X} (u : LB.Gen (CmpLB D₁ D₂ a χ₁ χ₂)) : Prop :=
  u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good (JN D₁ D₂) z J → val u (r ≫ eSec D₁.P.A) z J = 1

def Act (D₁ D₂ : DegPre R) (a : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : GtPtF D₁ F) (g' : GtPtF D₂ F) : Prop :=
  g'.b = g.b ≫ a ∧ ∀ (χ : D₂.X) (u : LB.Gen (CmpLB D₁ D₂ a (h χ) χ)), Nrm u → ∀ z J, Good (JN D₁ D₂) z J →
    val (g'.s χ) (𝟙 _) z (rr J) = val (g.s (h χ)) (𝟙 _) z (rl J) * val u g.b.left z J

variable {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

def Over₀ (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) : Prop :=
  ∀ e, (Over.pullback (thick R I e)).map a ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map b

def OnTorus (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (h : D₂.toPre.X → D₁.toPre.X) : Prop :=
  ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
    TorusHomOf h t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map a = t ≫ (U₂.gt e).i

def Lin (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  IsMonHom a ∧ IsMonHom b ∧ Over₀ U₁ U₂ a b ∧ OnTorus U₁ U₂ a h

def Coord (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ), Nrm u ∧
    ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) =
        val ((U₁.gt e).t (h χ)) x z (rl J) * val u (x ≫ (U₁.gt e).pG.left) z J

def Gen₀ (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) : Prop :=
  (Over.pullback (jK R)).map a ≫ U₂.gen.hom = U₁.gen.hom ≫ c

def CrossH {F : Type} [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A) {j j' : ℕ} (t₁ t₂ : SecA A₂ F j)
    (t₁' t₂' : SecA A₁ F j') : Prop :=
  ∀ z J₁ J₂, Good A₁.L z J₁ → Good A₂.L z J₂ →
    sA t₁ (TFK (R := R) F ◁ c).left z J₂ * sA t₂' (𝟙 _) z J₁ = sA t₂ (TFK (R := R) F ◁ c).left z J₂ * sA t₁' (𝟙 _) z J₁

def Key (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D₁.toPre F k) (x : TFK (R := R) F ⟶ A₁.A), QkToAkU U₁ F k p x →
    ∀ g', Act D₁.toPre D₂.toPre b h p.g g' → ∃ p' : QkPt D₂.toPre F k, p'.g = g' ∧ QkToAkU U₂ F k p' (x ≫ c)

theorem lin_of_endU {U : UnifPre I D₁ A₁ G₁} (E : EndU U) : Lin U U E.aG E.aB E.h ∧ Gen₀ U U E.aG E.aA :=
  ⟨⟨E.homG, E.homB, E.q_lin, E.i_lin⟩, E.ext⟩

end GlobalTheory.Mum.Two
