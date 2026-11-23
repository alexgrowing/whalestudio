import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsTranslA (f : D.La →+ D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ (∀ x, o'.eta x = o.eta (f x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSubA o f N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

theorem IsTranslA.eta {f : D.La →+ D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsTranslA f c k N o o' ψ) (x : D.La) : o'.eta x = o.eta (f x) ≫ ψ :=
  h.2.2.1 x

theorem IsTranslA.dvd {f : D.La →+ D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsTranslA f c k N o o' ψ) : c ∣ k ^ 2 :=
  h.2.2.2.2.2

example (f : D.La →+ D.La) (N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * 3) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) :
    ¬ IsTranslA f 5 3 N o o' ψ :=
  fun h => absurd h.dvd (by decide)

end GlobalTheory.UPel.HT.HeckeAd
