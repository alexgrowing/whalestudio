import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.OrbMark

theorem exists_semilinear_pull_of_evalZ_eq_one : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  intro O _ w0 X₀ _ _ v X _ _ _ β h1
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun] at h1
  split_ifs at h1 with hc
  swap
  · exact absurd h1 zero_ne_one
  obtain ⟨-, σ, hσ, s, hs, H⟩ := hc

  let g : (Fin n → O) →+ X :=
    { toFun := fun a => r (twv σ a)
      map_zero' := by rw [twv_zero, map_zero]
      map_add' := fun a b => by
        have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
        rw [e, map_add] }
  have hg : ∀ a, g a = r (twv σ a) := fun _ => rfl
  have hgs : ∀ (c : O) a, g (c • a) = σ c • g a := fun c a => by
    rw [hg, hg, twv_smul, map_smul]
  have hgsurj : Function.Surjective g := fun x => by
    obtain ⟨a, ha⟩ := hr x
    exact ⟨twv σ.symm a, by rw [hg, twv_twv_symm, ha]⟩
  have hker : ∀ z, g z = 0 → s z = 0 := by
    intro z hz
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
    rw [← hx]
    refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
    obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
    have h1 := H (c • z) b (c • x) y
      (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
    have e : r (twv σ (c • z)) = 0 := by rw [← hg, hgs, hz, smul_zero]
    dsimp only at h1
    rw [e, map_zero, LinearMap.zero_apply] at h1
    exact_mod_cast h1.symm
  have hwd : ∀ a a', g a = g a' → s a = s a' := fun a a' h => by
    have := hker (a - a') (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let pre : X → (Fin n → O) := fun x => (hgsurj x).choose
  have hpre : ∀ x, g (pre x) = x := fun x => (hgsurj x).choose_spec
  have hf : ∀ a, s (pre (g a)) = s a := fun a => hwd _ _ (hpre _)
  let f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
    { toFun := fun x => s (pre x)
      map_zero' := by
        have := hf 0
        rw [map_zero] at this
        rw [this, map_zero]
      map_add' := fun x y => by
        have := hf (pre x + pre y)
        rw [map_add, hpre, hpre] at this
        rw [this, map_add] }
  have hfg : ∀ a, f (g a) = s a := hf
  refine ⟨σ.symm, f, by rw [RingEquiv.symm_apply_eq, hσ], fun q => ?_, fun c x => ?_, fun x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨a, rfl⟩ := hs q
    exact ⟨g a, hfg a⟩
  · obtain ⟨a, rfl⟩ := hgsurj x
    have e : c • g a = g (σ.symm c • a) := by rw [hgs, σ.apply_symm_apply]
    rw [e, hfg, hfg, map_smul]
  · obtain ⟨a, rfl⟩ := hgsurj x
    obtain ⟨b, rfl⟩ := hgsurj y
    rw [hfg] at hx hy
    have h := H a b x₀ y₀ hx hy
    dsimp only at h
    rw [← hg, ← hg] at h
    exact_mod_cast h

end GlobalTheory.PolFan.OrbMark
