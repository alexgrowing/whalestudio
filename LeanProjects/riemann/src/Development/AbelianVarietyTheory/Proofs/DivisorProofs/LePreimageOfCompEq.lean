import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_le_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) :
    α ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hW hy

theorem locInt_le_gen {S G Y T : Scheme.{0}} (g : G ⟶ S) (α : Y ⟶ G) (t : Y ⟶ T) (e : T ⟶ S)
    (hpb : α ≫ g = t ≫ e) (W : G.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) :
    α ⁻¹ᵁ W ≤ t ⁻¹ᵁ (e ⁻¹ᵁ U) := by
  intro y hy
  have h1 : g (α y) ∈ U := hWU hy
  have h2 : (α ≫ g) y = (t ≫ e) y := by rw [hpb]
  show e (t y) ∈ U
  rw [← Scheme.Hom.comp_apply, ← h2]
  exact h1

def LocInt {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left) {Y : Scheme.{0}}
    (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : α ≫ G.hom = t ≫ M.gp) {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens) (hW : W ≤ L.U j) (hWU : W ≤ G.hom ⁻¹ᵁ U),
    IsAffineOpen W → IsAffineOpen U →
    ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)),
      (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j)) =
        ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb W U hWU)).hom (b m)

theorem le_preimage_of_comp_eq {X X' S : Scheme.{0}} (g : X ⟶ S) (g' : X ⟶ X') (h : X' ⟶ S) (e : g' ≫ h = g)
    (U : S.Opens) : g ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ U) := by
  intro x hx
  show h (g' x) ∈ U
  rw [← Scheme.Hom.comp_apply, e]
  exact hx

end GlobalTheory.Mum
