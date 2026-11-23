import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem bijective_of_surjective_of_VB : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B,
    Function.Surjective f → Function.Bijective f := by
  intro R A B _ _ _ _ _ n hA hB f hf
  obtain ⟨fA, pA, rA⟩ := hA
  obtain ⟨fB, pB, rB⟩ := hB
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hg' : ∀ b, f (g b) = b := fun b => LinearMap.congr_fun hg b

  let s : A →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - g ∘ₗ f) (fun a => by
      simp [LinearMap.mem_ker, hg'])
  have hs : s ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    have hx : f x.1 = 0 := x.2
    simp [s, hx]
  have hsurj : Function.Surjective s := fun x => ⟨x.1, LinearMap.congr_fun hs x⟩
  haveI : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective s hsurj
  haveI : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype s hs

  let E : (LinearMap.ker f × B) ≃ₗ[R] A :=
    LinearEquiv.ofLinear ((LinearMap.ker f).subtype.coprod g) (s.prod f)
      (by
        ext a <;> simp [s, hg'])
      (by
        ext x <;> simp [s, hg'])
  have hsub : Subsingleton (LinearMap.ker f) := by
    rw [← Module.rankAtStalk_eq_zero_iff_subsingleton (R := R)]
    funext p
    have h1 := congrFun (Module.rankAtStalk_prod (R := R) (LinearMap.ker f) B) p
    have h2 := Module.rankAtStalk_eq_of_equiv (R := R) E
    have h3 := congrFun h2 p
    simp only [Pi.add_apply] at h1
    rw [h1, rA p, rB p] at h3
    simpa using h3
  refine ⟨?_, hf⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : (⟨a, ha⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

end GlobalTheory.CompanionTheory.WedgeOf
