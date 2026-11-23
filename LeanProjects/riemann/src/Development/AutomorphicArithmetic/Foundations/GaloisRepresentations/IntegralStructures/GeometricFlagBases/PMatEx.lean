import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.matEx_of :
    MatEx := by
  intro Γ L _ _ M _ _ a h1 hmul U hU d b
  let f : Γ → (U →ₗ[L] U) := fun g => (a g).restrict (fun x hx => hU g x hx)
  have hfv : ∀ g (x : U), ((f g x : U) : M) = a g (x : M) := fun g x => rfl
  have hf1 : f 1 = LinearMap.id := by
    ext x
    simp [hfv, h1]
  have hfm : ∀ g h, f (g * h) = f g ∘ₗ f h := by
    intro g h
    ext x
    simp [hfv, hmul]
  let φ : Γ →* Matrix (Fin d) (Fin d) L :=
    { toFun := fun g => LinearMap.toMatrix b b (f g)
      map_one' := by
        simp only [hf1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        simp only [hfm]
        exact LinearMap.toMatrix_comp b b b (f g) (f h) }
  let ρ : Γ →* GL (Fin d) L := φ.toHomUnits
  have hρ : ∀ g, ((ρ g : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = LinearMap.toMatrix b b (f g) :=
    fun g => MonoidHom.coe_toHomUnits φ g
  refine ⟨ρ, ?_, ?_⟩
  · intro g j
    simp only [hρ, LinearMap.toMatrix_apply]
    rw [← hfv]
    have e := congrArg Subtype.val (b.sum_repr (f g (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    exact e.symm
  · intro i j
    obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (b.coord i)
    refine ⟨μ, fun g => ?_⟩
    rw [hρ, LinearMap.toMatrix_apply, ← hfv]
    have hc : μ (U.subtype (f g (b j))) = b.coord i (f g (b j)) := by
      rw [← LinearMap.comp_apply, hμ]
    rw [Module.Basis.coord_apply] at hc
    exact hc.symm
