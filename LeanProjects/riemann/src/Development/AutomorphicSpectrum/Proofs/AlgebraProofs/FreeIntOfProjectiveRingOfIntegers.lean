import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProIsometryOfLocalIsometriesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmProjectiveModulePairingPStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIsometryEquivarianceStatement

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem finite_int_of_finite_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] : Module.Finite ℤ L :=
  Module.Finite.trans (𝓞 E) L

theorem free_int_of_projective_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Free ℤ L := by
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) L)
  have hinj : Function.Injective s := fun x y hxy => by
    have := congrArg (Finsupp.linearCombination (𝓞 E) id) hxy
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  haveI : Module.IsTorsionFree ℤ (L →₀ 𝓞 E) := inferInstance
  haveI : Module.IsTorsionFree ℤ L :=
    hinj.moduleIsTorsionFree (R := ℤ) s fun r m => by simp
  infer_instance

theorem proIso_of_unimodular_alternating :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → Nonempty (ProIso (𝓞 E) B B') := by
  intro E _ _ _ bar hbar hun L L' _ _ _ _ _ _ _ _ B B' hrk hB hBb hBa hB' hBb' hBa'
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  haveI : Module.Finite ℤ L' := finite_int_of_finite_ringOfIntegers E L'
  haveI : Module.Free ℤ L := free_int_of_projective_ringOfIntegers E L
  haveI : Module.Free ℤ L' := free_int_of_projective_ringOfIntegers E L'
  refine GlobalTheory.T.pro_isometry_of_local_isometries (𝓞 E) L L' B B' fun p hp => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, h1, h2⟩ := GlobalTheory.T.cm_projective_module_pairing_p E bar hbar hun p L L' B B' hrk hB hBb hBa hB' hBb' hBa'
  exact GlobalTheory.T.padic_isometry_equivariance p (𝓞 E) L L' B B' φ h1 h2

end GlobalTheory.CompanionTheory.Ar
