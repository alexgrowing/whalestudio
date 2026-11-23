import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_isBaseChange : ∀ (K L Γ V W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ : Representation K Γ V) (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K L Γ V W _ _ _ _ _ _ _ _ _ _ _ f hf ρ ρ' hρ H n hE
  obtain ⟨j, hj, hje⟩ := hE
  let eK : MonoidAlgebra K H ≃ₗ[K] (H →₀ K) := MonoidAlgebra.coeffLinearEquiv K
  let eL : MonoidAlgebra L H ≃ₗ[L] (H →₀ L) := MonoidAlgebra.coeffLinearEquiv L
  let m0 : (H →₀ K) →ₗ[K] (H →₀ L) := Finsupp.mapRange.linearMap (Algebra.linearMap K L)
  let φ0 : MonoidAlgebra K H →ₗ[K] MonoidAlgebra L H :=
    (eL.restrictScalars K).symm.toLinearMap ∘ₗ m0 ∘ₗ eK.toLinearMap
  have h0 : IsBaseChange L φ0 := by
    refine (IsBaseChange.iff_of_equiv_comm eK eL (f' := m0) ?_).mpr
      (IsBaseChange.finsuppPow H (IsBaseChange.linearMap K L))
    exact LinearMap.ext fun x => (eL.apply_symm_apply (m0 (eK x))).symm
  have hφ0 : ∀ x, φ0 x = MonoidAlgebra.mapRingHom H (algebraMap K L) x := by
    intro x
    ext g
    simp [φ0, eK, eL, m0]
  let φ : (Fin n → MonoidAlgebra K H) →ₗ[K] (Fin n → MonoidAlgebra L H) := φ0.compLeft (Fin n)
  have hφ : IsBaseChange L φ := IsBaseChange.finitePow (Fin n) h0
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  let j' : W →ₗ[L] (Fin n → MonoidAlgebra L H) := hf.lift (φ ∘ₗ j)
  have hj'f : ∀ v, j' (f v) = φ (j v) := fun v => hf.lift_eq _ v
  let P : (Fin n → MonoidAlgebra L H) →ₗ[L] W := hφ.lift (f ∘ₗ p)
  have hPj : ∀ w, P (j' w) = w := by
    intro w
    have : P ∘ₗ j' = LinearMap.id := hf.algHom_ext _ _ (fun v => by
      rw [LinearMap.comp_apply, hj'f]
      change hφ.lift (f ∘ₗ p) (φ (j v)) = f v
      rw [hφ.lift_eq, LinearMap.comp_apply, ← LinearMap.comp_apply p j, hp, LinearMap.id_apply])
    exact LinearMap.congr_fun this w
  refine ⟨j', fun a b hab => by rw [← hPj a, ← hPj b, hab], ?_⟩
  intro h w i
  have key : (LinearMap.proj i ∘ₗ j' ∘ₗ (ρ' h)) =
      (LinearMap.mulLeft L (MonoidAlgebra.single h (1 : L)) ∘ₗ LinearMap.proj i ∘ₗ j') := by
    refine hf.algHom_ext _ _ (fun v => ?_)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply, hρ, hj'f]
    change φ0 (j (ρ h v) i) = MonoidAlgebra.single h 1 * φ0 (j v i)
    rw [hje, hφ0, hφ0, map_mul, MonoidAlgebra.mapRingHom_single, map_one]
  exact LinearMap.congr_fun key w

end GlobalTheory.BadCount
