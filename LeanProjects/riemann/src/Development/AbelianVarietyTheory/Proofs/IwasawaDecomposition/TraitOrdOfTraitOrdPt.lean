import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def TraitOrdPt (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (U : Z.X.Opens) (f : Γ(Z.X, U)) (x : Z.X) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t),
      Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
      ∀ hU : χ (closedPoint W) ∈ U, χ (closedPoint W) = x → ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧
        Associated ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.germ U _ hU).hom f)) (ϖ ^ n)

theorem traitOrd_of_traitOrdPt {φ : InvFun (𝓞 E)} {Z : Model Xo c β} {U : Z.X.Opens} {f : Γ(Z.X, U)}
    (h : ∀ x ∈ U, TraitOrdPt φ Z U f x) : TraitOrd φ Z U f :=
  fun W _ _ _ hW ϖ hϖ χ t m P hχ be hbe hmon hU => h _ hU W hW ϖ hϖ χ t m P hχ be hbe hmon hU rfl

theorem TraitOrdPt.of_associated {φ : InvFun (𝓞 E)} {Z : Model Xo c β} {U V : Z.X.Opens} {f : Γ(Z.X, U)}
    {g : Γ(Z.X, V)} {x : Z.X} (hx : x ∈ U) (hx' : x ∈ V)
    (ha : Associated ((Z.X.presheaf.germ U x hx).hom f) ((Z.X.presheaf.germ V x hx').hom g))
    (hg : TraitOrdPt φ Z V g x) : TraitOrdPt φ Z U f x := by
  intro W _ _ _ hW ϖ hϖ χ t m P hχ be hbe hmon hU hcx
  subst hcx
  obtain ⟨n, hn, hgn⟩ := hg W hW ϖ hϖ χ t m P hχ be hbe hmon hx' rfl
  exact ⟨n, hn, (ha.map (Scheme.stalkClosedPointTo χ).hom).trans hgn⟩

end GlobalTheory.TorRef
