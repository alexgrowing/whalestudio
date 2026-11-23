import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyMapEqOfInnerConj

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem ptH_comp_permMap_eq : ∀ (k G H H' X Y : Type) [CommRing k] [Group G] [Group H] [Group H'] [MulAction G X] [MulAction G Y] (φ : H →* G) (φ' : H' →* G) (σ : H' →* H) (x : X) (hx : ∀ h, φ' h • x = x) (y : Y) (hy : ∀ h, φ h • y = y) (f : X → Y) (hf : ∀ (g : G) z, f (g • z) = g • f z) (g : G), φ.comp σ = φ' → g • f x = y → (∀ h, g * φ' h = φ' h * g) → ∀ n : ℕ, ptH k φ' x hx n ≫ hMap (permMap f hf (Rep.trivial k G k)) n = groupHomology.map (A := Rep.trivial k H' k) (B := Rep.trivial k H k) σ (𝟙 (Rep.trivial k H' k)) n ≫ ptH k φ y hy n := by
  intro k G H H' X Y _ _ _ _ _ _ φ φ' σ x hx y hy f hf g hσ hgy hc n
  subst hσ
  have hfx : ∀ h, (φ.comp σ) h • f x = f x := fun h => by rw [← hf, hx]
  have hy' : ∀ h, (φ.comp σ) h • y = y := fun h => hy (σ h)
  have h1 := groupHomology.map_comp (A := Rep.trivial k H' k) (B := perm k G X) (C := perm k G Y)
    (φ.comp σ) (MonoidHom.id G) (ptMap (φ.comp σ) x hx (Rep.trivial k G k))
    (permMap f hf (Rep.trivial k G k)) n
  have hmor : (ptMap (φ.comp σ) x hx (Rep.trivial k G k) ≫
      (Rep.resFunctor (φ.comp σ)).map (permMap f hf (Rep.trivial k G k)) :
        Rep.trivial k H' k ⟶ Rep.res (φ.comp σ) (perm k G Y)) =
      ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k) := by
    ext a
    change (Finsupp.mapDomain f (Finsupp.single x (1:k))) a = (Finsupp.single (f x) (1:k)) a
    rw [Finsupp.mapDomain_single]
  have hL : ptH k (φ.comp σ) x hx n ≫ hMap (permMap f hf (Rep.trivial k G k)) n =
      groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k)) n :=
    h1.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor)
  have h2 := groupHomology.map_comp (A := Rep.trivial k H' k) (B := Rep.trivial k H k) (C := perm k G Y)
    σ φ (𝟙 (Rep.trivial k H' k)) (ptMap φ y hy (Rep.trivial k G k)) n
  have hmor2 : (𝟙 (Rep.trivial k H' k) ≫ (Rep.resFunctor σ).map (ptMap φ y hy (Rep.trivial k G k)) :
        Rep.trivial k H' k ⟶ Rep.res (φ.comp σ) (perm k G Y)) =
      ptMap (φ.comp σ) y hy' (Rep.trivial k G k) := by
    ext a
    rfl
  have hR : groupHomology.map (A := Rep.trivial k H' k) (B := Rep.trivial k H k) σ
      (𝟙 (Rep.trivial k H' k)) n ≫ ptH k φ y hy n =
      groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) y hy' (Rep.trivial k G k)) n :=
    h2.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor2)
  rw [hL, hR]
  symm
  refine GlobalTheory.HomStab.groupHomology_map_conj k G H' (Rep.trivial k H' k) (perm k G Y) (φ.comp σ) (φ.comp σ)
    (ptMap (φ.comp σ) (f x) hfx (Rep.trivial k G k)) (ptMap (φ.comp σ) y hy' (Rep.trivial k G k)) g
    (fun h => by rw [hc h, mul_inv_cancel_right]) (fun a => ?_) n
  subst hgy
  change Finsupp.single (g • f x) a = Finsupp.mapDomain (fun z => g • z) (Finsupp.mapRange id rfl (Finsupp.single (f x) a))
  rw [Finsupp.mapRange_id, Finsupp.mapDomain_single]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
