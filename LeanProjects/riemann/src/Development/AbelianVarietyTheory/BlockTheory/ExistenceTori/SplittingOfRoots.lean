import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingOfRoots

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def RootsExist : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La),
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
      (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))),
      φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧
      ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b)

def GeoExhaust {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  ∀ (k : Type) [Field k] (ψ : S →+* k) (g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0), g.left = spMap ψ →
    ∀ a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G), InZh Xo Λ N a → ∃ i, ∀ b, a b = g ≫ z i b

def IsSplitBy {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo x0 z ∧ GeoExhaust Xo Λ N x0 z

def ZSplits : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
      ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
        (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)),
        φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsSplitBy Xo Λ N y'.x z

def RootsAndSplitting : Prop := RootsExist Xo c ∧ ZSplits Xo c

example (n : ℕ) : GenLat.LevOK (⟨stdLat E n⟩ : GenLat E n) l.M l.M := by
  refine ⟨l.odd, dvd_rfl, ?_⟩
  simp only [GenLat.Ln, inf_idem]
  exact Submodule.smul_le_right

example (Λ : GenLat E 0) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) :
    GeoExhaust Xo Λ N x0 (fun (_ : Unit) (b : Fin 0) => b.elim0) :=
  fun _ _ _ _ _ _ _ => ⟨(), fun b => b.elim0⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingOfRoots
