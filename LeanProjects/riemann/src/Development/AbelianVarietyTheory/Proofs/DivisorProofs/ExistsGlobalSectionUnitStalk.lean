import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.DivGlue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG exists_chart)

theorem resG_app {Y Z : Scheme.{0}} (ι : Y ⟶ Z) {U U' : Z.Opens} (e : U' ≤ U) {V : Y.Opens}
    (h : V ≤ ι ⁻¹ᵁ U') (h' : V ≤ ι ⁻¹ᵁ U) (x : Γ(Z, U)) :
    resG Y h' ((ι.app U).hom x) = resG Y h ((ι.app U').hom (resG Z e x)) := by
  have h1 : ι.app U ≫ Y.presheaf.map (homOfLE h').op = ι.appLE U V h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 : Z.presheaf.map (homOfLE e).op ≫ ι.app U' ≫ Y.presheaf.map (homOfLE h).op =
      ι.appLE U V h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact (congrArg (fun f => f.hom x) h1).trans (congrArg (fun f => f.hom x) h2).symm

theorem glue : ∀ (Y Z : Scheme.{0}) (ι : Y ⟶ Z) (D : LB Z), D.IsLB → ∀ t : (D.pull ι).Gen, t.IsGen →
  ∀ (M : ℕ) (a : ∀ i, Γ(Z, D.U i)),
  (∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) * ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j)) →
  ∃ h : Γ(Y, ⊤), ∀ (i : D.ι) (y : Y) (hy : ι y ∈ D.U i), ∃ u : (Y.presheaf.stalk y)ˣ,
    (Y.presheaf.germ ⊤ y trivial).hom h = (ι.stalkMap y).hom ((Z.presheaf.germ (D.U i) (ι y) hy).hom (a i)) * (u : Y.presheaf.stalk y) := by
  intro Y Z ι D hD t ht M a ha
  let j : D.ι → (PUnit → D.ι) := fun i _ => i
  let W : D.ι → Y.Opens := fun i => (D.pull ι).U (j i)
  have hW : ∀ i, W i ≤ ι ⁻¹ᵁ D.U i := fun i => LB.wchart_le D _ (j i) PUnit.unit
  let b : ∀ i, Γ(Y, W i) := fun i =>
    resG Y (hW i) ((ι.app (D.U i)).hom (a i)) * ((t.s (j i) ^ M : Γ(Y, (D.pull ι).U (j i))ˣ) : Γ(Y, (D.pull ι).U (j i)))
  have cover : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart hD (ι y)
    exact Opens.mem_iSup.2 ⟨i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨h, hh⟩ := GlobalTheory.LB.exists_fun_of_cover W (fun _ => le_top) cover b (by
    intro i i'
    have hV : W i ⊓ W i' ≤ ι ⁻¹ᵁ (D.U i ⊓ D.U i') := fun y hy => ⟨hW i hy.1, hW i' hy.2⟩
    have hA := congrArg (fun x => resG Y hV ((ι.app _).hom x)) (ha i i')
    simp only [map_mul, map_pow] at hA
    simp only [b, map_mul, GlobalTheory.LB.resG_resG]
    rw [← GlobalTheory.LB.val_res, ← GlobalTheory.LB.val_res, map_pow, map_pow, ht (j i) (j i'), mul_pow, Units.val_mul]
    have hG : (((D.pull ι).g (j i) (j i') : Γ(Y, W i ⊓ W i')ˣ) : Γ(Y, W i ⊓ W i')) =
        resG Y hV ((ι.app _).hom (D.g i i' : Γ(Z, D.U i ⊓ D.U i'))) := by
      show ((∏ _k : PUnit, (res hV (pullU ι _ (D.g i i'))) ^ (1 : ℤ) : Γ(Y, W i ⊓ W i')ˣ) :
        Γ(Y, W i ⊓ W i')) = _
      rw [Finset.univ_unique, Finset.prod_singleton, zpow_one]
      rfl
    rw [Units.val_pow_eq_pow_val, hG, resG_app ι inf_le_left hV, resG_app ι inf_le_right hV, ← hA]
    ring)
  refine ⟨h, fun i y hy => ?_⟩
  have hyW : y ∈ W i := Set.mem_iInter.2 fun _ => hy
  refine ⟨Units.map (Y.presheaf.germ (W i) y hyW).hom.toMonoidHom (t.s (j i) ^ M), ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (le_top : W i ≤ ⊤)) y hyW h]
  change (Y.presheaf.germ (W i) y hyW).hom (resG Y le_top h) = _
  rw [hh i, map_mul]
  congr 1
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact Y.presheaf.germ_res_apply (homOfLE (hW i)) y hyW _

end GlobalTheory.DivGlue
