import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem thetaFin_mono {C : Subgroup 𝓀[k]ˣ} {x : kˣ} (h : x ∈ unitsC k C) : x ∈ unitsC k ⊤ := by
  obtain ⟨d, -, rfl⟩ := h
  exact ⟨d, trivial, rfl⟩

private theorem thetaFin_one {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : Representation A (GL (Fin n) k) M) (C : Subgroup 𝓀[k]ˣ) (θ) (hθ : IsTheta ρ C θ) (t : Fin n → kˣ)
    (ht : ∀ i, t i ∈ unitsC k C) : θ t = 1 := by
  have hd : Dom t := fun a b _ => le_of_eq (by
    rw [((memIwC k n ⊤).2.2.2 _).1 (thetaFin_mono (ht a)), ((memIwC k n ⊤).2.2.2 _).1 (thetaFin_mono (ht b))])
  have hm : diagT k (Fin n) t ∈ iwC k n C := Subgroup.mem_sup_right ⟨_, fun i' _ => ht i', rfl⟩
  have hn : diagT k (Fin n) t ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := Subgroup.le_normalizer hm
  apply Units.ext
  rw [hθ t hd]
  ext v
  rw [(hkNorm A _ M ρ _ _ (heckePairIwC k n C).1 hn).1 v]
  exact v.2 _ hm

end Loc

theorem UpperTheory.V.Th.thetaFin :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (C C' : Subgroup 𝓀[k]ˣ) (θ), IsTheta ρ C θ → ∀ δ : kˣ, IsGenMod k C' δ → ∀ i : Fin n, ∃ m : ℕ, 0 < m ∧ θ (Pi.mulSingle i δ) ^ m = 1 := by
  intro k _ _ _ _ n A M _ _ _ ρ C C' θ hθ δ hδ i
  obtain ⟨d, rfl, -⟩ := hδ
  refine ⟨Nat.card 𝓀[k]ˣ, Nat.card_pos, ?_⟩
  rw [← map_pow]
  refine thetaFin_one ρ C θ hθ _ fun j => ?_
  rw [Pi.pow_apply]
  by_cases e : j = i
  · subst e
    rw [Pi.mulSingle_eq_same]
    refine ⟨d ^ Nat.card 𝓀[k]ˣ, ?_, map_pow _ _ _⟩
    show Units.map (residue 𝒪[k]).toMonoidHom _ ∈ C
    rw [map_pow, pow_card_eq_one']
    exact one_mem _
  · rw [Pi.mulSingle_eq_of_ne e, one_pow]
    exact one_mem _
