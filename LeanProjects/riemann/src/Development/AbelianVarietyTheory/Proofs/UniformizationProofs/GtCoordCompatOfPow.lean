import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowLevelCompat

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem box_gen_val_along {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε))
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  have hm : r y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i),
      Set.mem_iInter.2 fun a => hJ' (r ≫ φ' a)⟩
  have E := congrArg (gm r y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (r ≫ φ' a))))
    (H (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)))
  have E₁ := gm_linCombIso w φ' ε r y _ _ hm
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) E₁ (gm_res r y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res r y inf_le_left hm _).trans ?_))
  refine (map_prod (gm r y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i))))
    (fun i => res (GeneratorPullback.box_le M pr φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) i)
      ((GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => J ((r ≫ φ' a) ≫ pr i))))
      Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  rw [val_of (t i) (r ≫ ρ i) y J (fun a => J ((r ≫ φ' a) ≫ pr i))
    (fun a => congrArg J (by rw [Category.assoc, Category.assoc, hψ]))]
  have h₁ := GeneratorPullback.box_le M pr φ' _ i hm.1
  have h₂ : ρ i (r y) ∈ LB.wchart M (φ i) (fun a => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => (congrArg (fun g => g y ∈ M.U (J ((r ≫ φ' a) ≫ pr i)))
      (show (r ≫ φ' a) ≫ pr i = (r ≫ ρ i) ≫ φ i a by rw [Category.assoc, Category.assoc, hψ])).mp (hJ _)
  exact (gm_res r y (GeneratorPullback.box_le M pr φ' _ i) hm.1 _).trans ((gm_res r y _ h₁ _).trans (gm_pull r (ρ i) y _ h₂ _))

end PowLevelCompat

end GlobalTheory
