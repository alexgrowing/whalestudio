import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.isoSum_of_injective_equivariant_family :
    ∀ (H M N : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (ρ : Representation ℂ H M) (ρ' : Representation ℂ H N) (Y : Submodule ℂ M) (Z : Submodule ℂ N) (τ : SmIrr H) (I : Type) [Finite I] (φ : I → M →ₗ[ℂ] N), IsoSum ρ' Z τ → (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → (∀ i, ∀ y ∈ Y, φ i y ∈ Z) → (∀ i g, ∀ y ∈ Y, φ i (ρ g y) = ρ' g (φ i y)) → (∀ y ∈ Y, (∀ i, φ i y = 0) → y = 0) → IsoSum ρ Y τ := by
  intro H M N _ _ _ _ _ _ _ ρ ρ' Y Z τ I _ φ hZ hY hφ he hinj
  classical
  letI := Fintype.ofFinite I
  let π : Representation ℂ H Y := (⟨Y, fun g v hv => hY g v hv⟩ : Subrepresentation ρ).toRepresentation
  let P : Representation ℂ H (I → N) :=
    { toFun := fun g => (ρ' g).compLeft I
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let j : Y →ₗ[ℂ] (I → N) := LinearMap.pi fun i => φ i ∘ₗ Y.subtype
  have hj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hinj y y.2 fun i => congrFun hy i)
  have hs : ∀ i g x, LinearMap.single ℂ (fun _ : I => N) i (ρ' g x) = P g (LinearMap.single ℂ (fun _ : I => N) i x) := by
    intro i g x
    funext k
    change (Pi.single i (ρ' g x) : I → N) k = ρ' g ((Pi.single i x : I → N) k)
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  have hsing : ∀ i, ∀ z ∈ Z, LinearMap.single ℂ (fun _ : I => N) i z ∈
      ⨆ f : {f : τ.V →ₗ[ℂ] (I → N) // ∀ g v, f (τ.ρ g v) = P g (f v)}, LinearMap.range f.1 := by
    intro i z hz
    refine Submodule.iSup_induction _ (motive := fun z => LinearMap.single ℂ (fun _ : I => N) i z ∈ _) (hZ hz) ?_ ?_ ?_
    · rintro f _ ⟨s, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : I => N) i ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2.1, hs]; rfl⟩ ⟨s, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  have key := UpperTheory.V.PiLin.iso_sub τ.ρ π P τ.irred j hj (fun g y => funext fun i => he i g y y.2) (fun y => by
    rw [← Finset.univ_sum_single (j y)]
    exact Submodule.sum_mem _ fun i _ => hsing i _ (hφ i y y.2))
  intro y hy
  refine Submodule.iSup_induction _ (motive := fun z : Y => (z : M) ∈ _) (key ⟨y, hy⟩) ?_ ?_ ?_
  · rintro f _ ⟨s, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨Y.subtype ∘ₗ f.1, fun g v => ?_, ?_⟩ ⟨s, rfl⟩
    · exact congrArg Subtype.val (f.2 g v)
    · rintro _ ⟨v, rfl⟩; exact (f.1 v).2
  · exact zero_mem _
  · intro a b ha hb
    exact add_mem ha hb
