import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValAtSpecMap
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem exists_der_gen {R RC C N L U : Type} [CommRing R] [IsDomain R] [CommRing RC] [IsDomain RC] [Field C]
    [Algebra RC C] [AddCommGroup N] [Finite N] [AddCommGroup L] [Module R L] [AddCommGroup U] [Module R U]
    (σ : R →+* RC) (h1 : Function.Injective σ) (h2 : Function.Injective (algebraMap RC C))
    (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (σ r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} (hA : IsHopfOrder A) (p : ℕ) {g : ℕ} (θ : L →ₗ[R] omega A)
    (hθs : Function.Surjective θ) (hθk : ∀ w, θ w = 0 → ∃ u, w = p • u) (j : L →ₗ[R] U)
    (io : U →ₛₗ[σ] (Fin g → RC)) (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∃ Dv : M →ₗ[RC] ReciprocityTheory.PGsh.Up.LieDualModP p RC g, IsDerAt0 M Dv ∧
      ∀ (a : A) (f : M) (w : L), (∀ x, f.1 x = φ (a.1 (Multiplicative.ofAdd x))) → cotMap A a = θ w →
        Dv f = Submodule.Quotient.mk (io (j w)) := by
  letI : Algebra R RC := σ.toAlgebra
  let k₀ : L →ₗ[R] ReciprocityTheory.PGsh.Up.LieDualModP p RC g :=
    { toFun := fun w => Submodule.Quotient.mk (io (j w))
      map_add' := fun a b => by rw [map_add, map_add, Submodule.Quotient.mk_add]
      map_smul' := fun r a => by
        rw [map_smul, io.map_smulₛₗ, Submodule.Quotient.mk_smul]
        exact algebraMap_smul RC r _ }
  have hk : LinearMap.ker θ ≤ LinearMap.ker k₀ := by
    intro w hw
    obtain ⟨u, rfl⟩ := hθk w hw
    change Submodule.Quotient.mk (io (j (p • u))) = 0
    rw [map_nsmul, map_nsmul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul RC]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  let d₀ : omega A →ₗ[R] ReciprocityTheory.PGsh.Up.LieDualModP p RC g :=
    ((LinearMap.ker θ).liftQ k₀ hk) ∘ₗ (θ.quotKerEquivOfSurjective hθs).symm.toLinearMap
  have hd₀ : ∀ w, d₀ (θ w) = k₀ w := fun w => by
    have : (θ.quotKerEquivOfSurjective hθs).symm (θ w) = Submodule.Quotient.mk w :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [d₀, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨Dv, hD1, hD2⟩ := exists_der_ext h1 h2 φ hφ hA (d₀ ∘ₗ cotMap A)
    (fun a b => by simp only [LinearMap.comp_apply, cotMap_mul, map_add, map_smul]) M hM
  refine ⟨Dv, hD1, fun a f w hf hw => ?_⟩
  rw [hD2 a f hf, LinearMap.comp_apply, hw, hd₀]
  rfl

theorem cotMap_aug {R T : Type} [CommRing R] [CommGroup T] (A : Subalgebra R (T → R)) (a : augIdeal A) :
    cotMap A a.1 = (augIdeal A).toCotangent a := by
  have ha1 : a.1.1 1 = 0 := a.2
  exact cotMap_apply _ _ a (by rw [ha1, map_zero, sub_zero])

theorem cotMap_char {R T : Type} [CommRing R] [CommGroup T] (A : Subalgebra R (T → R)) (χ : T →* Rˣ)
    (hm : (fun t => ((χ t : Rˣ) : R)) ∈ A) : cotMap A ⟨_, hm⟩ = dlogChar A χ := by
  rw [OrderApi.dlogChar_of_mem _ _ hm]
  refine cotMap_apply _ _ _ ?_
  simp

end PositivityTheory.Xgn.TestGroupPoint
