import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

structure IsProdUnif (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (U : UnifPre I D A (G₁ ⊗ G₂))
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A) : Prop where
  gen_pr₁ : U.gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom
  gen_pr₂ : U.gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom
  wL : ∃ w : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left), w.IsGen
  q_pr₁ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₁ =
    (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ (U₁.gt e).q
  q_pr₂ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₂ =
    (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ (U₂.gt e).q
  i_pr₁ : ∀ (e : ℕ) (h : D₁.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = t ≫ (U₁.gt e).i
  i_pr₂ : ∀ (e : ℕ) (h : D₂.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = t ≫ (U₂.gt e).i

variable {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem IsProdUnif.linHom_fst (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₁ : D₁.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₁ y) = y) (h₂ : ∀ y, q₂ (j₁ y) = 0) : LinHom U U₁ p₁ j₁ (fst G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₁ e).symm, fun e => hU.i_pr₁ e j₁ h₁ h₂⟩

theorem IsProdUnif.linHom_snd (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₂ : D₂.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₂ y) = 0) (h₂ : ∀ y, q₂ (j₂ y) = y) : LinHom U U₂ p₂ j₂ (snd G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₂ e).symm, fun e => hU.i_pr₂ e j₂ h₁ h₂⟩

end GlobalTheory.MumProd
