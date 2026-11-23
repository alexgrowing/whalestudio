import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem exists_bilinForm_descend_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (hf : Function.Surjective f) (β : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x, f x = 0 → ∀ y, β x y = 0) (h2 : ∀ x, f x = 0 → ∀ y, β y x = 0) :
    ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  classical
  set g := Function.surjInv hf with hgdef
  have hg : ∀ y, f (g y) = y := Function.surjInv_eq hf
  have key1 : ∀ a b, f a = f b → ∀ y, β a y = β b y := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h1 (a - b) hk y
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have key2 : ∀ a b, f a = f b → ∀ y, β y a = β y b := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h2 (a - b) hk y
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨LinearMap.mk₂ ℤ (fun y y' => β (g y) (g y')) ?_ ?_ ?_ ?_, ?_⟩
  · intro y1 y2 y'
    rw [key1 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add, hg, hg, hg]), map_add,
      LinearMap.add_apply]
  · intro c y y'
    rw [key1 (g (c • y)) (c • g y) (by rw [map_zsmul, hg, hg]), map_smul, LinearMap.smul_apply]
  · intro y y1 y2
    rw [key2 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add, hg, hg, hg]), map_add]
  · intro c y y'
    rw [key2 (g (c • y')) (c • g y') (by rw [map_zsmul, hg, hg]), map_smul]
  · intro x y
    rw [LinearMap.mk₂_apply, key1 (g (f x)) x (hg _), key2 (g (f y)) y (hg _)]

end GlobalTheory
