import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2HeckeMap :
    ∀ (A M M' ι ι' : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (Y : Submodule A M) (Y' : Submodule A M') (op : ι → Module.End A M) (op' : ι' → Module.End A M') [Fact (CommOn Y op)] [Fact (CommOn Y' op')] (φ : Y →ₗ[A] Y') (j : ι' → ι), Function.Injective φ → (∀ i (y : Y), ((φ ((heckeGen Y op (j i) : Module.End A Y) y) : Y') : M') = op' i (φ y)) → ∃ ψ : heckeAlg Y' op' →ₐ[A] heckeAlg Y op, (∀ i, ψ (heckeGen Y' op' i) = heckeGen Y op (j i)) ∧ ∀ (t : heckeAlg Y' op') (y : Y), φ ((ψ t : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
  intro A M M' ι ι' _ _ _ _ _ Y Y' op op' _ _ φ j hφ hop
  have uniq : ∀ (t : Module.End A Y') (s s' : heckeAlg Y op),
      (∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)) → (∀ y : Y, φ ((s' : Module.End A Y) y) = t (φ y)) → s = s' := by
    intro t s s' h h'
    exact Subtype.ext (LinearMap.ext fun y => hφ ((h y).trans (h' y).symm))
  have ex : ∀ t : heckeAlg Y' op', ∃ s : heckeAlg Y op,
      ∀ y : Y, φ ((s : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
    rintro ⟨t, ht⟩
    change ∃ s : heckeAlg Y op, ∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      exact ⟨heckeGen Y op (j i), fun y => Subtype.ext ((hop i y).trans (hi (φ y)).symm)⟩
    | algebraMap r =>
      refine ⟨algebraMap A _ r, fun y => ?_⟩
      change φ (r • y) = r • φ y
      exact map_smul φ r y
    | add a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s + s', fun y => ?_⟩
      change φ ((s : Module.End A Y) y + (s' : Module.End A Y) y) = a (φ y) + b (φ y)
      rw [map_add, hs, hs']
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s * s', fun y => ?_⟩
      change φ ((s : Module.End A Y) ((s' : Module.End A Y) y)) = a (b (φ y))
      rw [hs, hs']
  choose f hf using ex
  refine ⟨{ toFun := f
            map_one' := uniq _ _ _ (hf 1) fun y => rfl
            map_mul' := fun a b => uniq _ _ _ (hf (a * b)) fun y => ?_
            map_zero' := uniq _ _ _ (hf 0) fun y => map_zero φ
            map_add' := fun a b => uniq _ _ _ (hf (a + b)) fun y => ?_
            commutes' := fun r => uniq _ _ _ (hf (algebraMap A _ r)) fun y => map_smul φ r y }, fun i => ?_, hf⟩
  · change φ ((f a : Module.End A Y) ((f b : Module.End A Y) y)) = (a : Module.End A Y') ((b : Module.End A Y') (φ y))
    rw [hf, hf]
  · change φ ((f a : Module.End A Y) y + (f b : Module.End A Y) y) = (a : Module.End A Y') (φ y) + (b : Module.End A Y') (φ y)
    rw [map_add, hf, hf]
  · exact uniq _ _ _ (hf (heckeGen Y' op' i)) fun y => Subtype.ext (hop i y)
