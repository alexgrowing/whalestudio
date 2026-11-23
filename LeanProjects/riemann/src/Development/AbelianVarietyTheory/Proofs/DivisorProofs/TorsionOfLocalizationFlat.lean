import Mathlib
open TensorProduct

namespace GlobalTheory

theorem kernel_rTensor_subtype_powers_torsion (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M] :
  Module.Flat (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) →
  ∀ (I : Ideal A) (y : TensorProduct A I M), I.subtype.rTensor M y = 0 → ∃ k : ℕ, f ^ k • y = 0 := by
  intro hfl I y hy
  set S := Submonoid.powers f
  set g := LocalizedModule.mkLinearMap S M
  haveI : Module.Flat A (LocalizedModule S M) := Module.Flat.trans A (Localization.Away f) _
  have hinj : Function.Injective (I.subtype.rTensor (LocalizedModule S M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hsq : (I.subtype.rTensor (LocalizedModule S M)) ((g.lTensor I) y) = (g.lTensor A) (I.subtype.rTensor M y) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have h0 : g.lTensor I y = 0 := hinj (by rw [hsq, hy, map_zero, map_zero])

  let e := TensorProduct.comm A I M
  have hl : IsLocalizedModule S (AlgebraTensorModule.rTensor A I g) := inferInstance
  have h1 : AlgebraTensorModule.rTensor A I g (e y) = 0 := by
    have key : ∀ z : TensorProduct A I M, AlgebraTensorModule.rTensor A I g (e z) = TensorProduct.comm A I (LocalizedModule S M) (g.lTensor I z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [e]
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    rw [key, h0, map_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff S (AlgebraTensorModule.rTensor A I g)).mp h1
  obtain ⟨k, hk⟩ := c.2
  refine ⟨k, ?_⟩
  have : e ((c : A) • y) = 0 := by rw [map_smul]; exact hc
  have hk' : f ^ k = (c : A) := hk
  rw [hk']
  exact e.injective (by rw [this, map_zero])

end GlobalTheory
