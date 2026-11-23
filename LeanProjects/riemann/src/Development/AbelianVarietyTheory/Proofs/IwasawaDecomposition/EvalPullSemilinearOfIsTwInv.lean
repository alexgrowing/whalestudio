import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eval_pull_semilinear_of_isTwInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
    IsTwInv H φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
      [Module.Finite (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E), τ H.w0 = H.w0 → ∀ (f : X →+ Y), Function.Surjective f →
      (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro E _ _ _ H φ htw X Y _ _ _ _ _ _ τ hτ f hf hsm B
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  let r₁ : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y :=
    { toFun := fun a => f (r (twv τ.symm a))
      map_add' := fun a b => by
        have e : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := funext fun _ => map_add τ.symm _ _
        rw [e, map_add, map_add]
      map_smul' := fun c a => by
        rw [twv_smul, map_smul, hsm, RingEquiv.apply_symm_apply]
        rfl }
  have hr₁ : ∀ a, r₁ (twv τ a) = f (r a) := fun a => by
    show f (r (twv τ.symm (twv τ a))) = f (r a)
    rw [twv_symm_twv]
  have hs₁ : Function.Surjective r₁ := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨twv τ a, hr₁ a⟩
  rw [φ.eval_eq hr, φ.eval_eq hs₁]
  have h := htw τ hτ n fun a b => B (r₁ a) (r₁ b)
  have e : (fun a b : Fin n → 𝓞 E => B (f (r a)) (f (r b))) = fun a b => B (r₁ (fun i => τ (a i))) (r₁ (fun i => τ (b i))) := by
    funext a b
    exact congrArg₂ B (hr₁ a).symm (hr₁ b).symm
  rw [e]
  exact h

end OrbMark

end GlobalTheory.PolFan
