import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory

theorem exists_finset_eval_injective {Z : Type} (T : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ T] :
    ∃ Y : Finset Z, ∀ g ∈ T, (∀ y ∈ Y, g y = 0) → g = 0 := by
  classical
  let φ : Z → Module.Dual ℂ T := fun z => (LinearMap.proj z).comp T.subtype
  have hfg : (Submodule.span ℂ (Set.range φ)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs', hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [← Set.image_univ] at hs'
  obtain ⟨Y, -, rfl⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨Y, fun g hg hY => ?_⟩
  have hle : Submodule.span ℂ (Set.range φ) ≤ LinearMap.ker (Module.Dual.eval ℂ T ⟨g, hg⟩) := by
    rw [hspan, Submodule.span_le]
    intro ψ hψ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    simp [φ, hY y hy]
  funext z
  have hz := hle (Submodule.subset_span ⟨z, rfl⟩)
  simpa [φ] using hz

theorem finiteDimensional_span_separately (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type)
    (S : ∀ i, Submodule ℂ (X i → ℂ)) (hS : ∀ i, FiniteDimensional ℂ (S i)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}) := by
  classical
  choose Y hY using fun i => @exists_finset_eval_injective (X i) (S i) (hS i)
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}
      add_mem' := fun {f g} hf hg i x => (S i).add_mem (hf i x) (hg i x)
      zero_mem' := fun i x => (S i).zero_mem
      smul_mem' := fun c f hf i x => (S i).smul_mem c (hf i x) }
  have hle : Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i} ≤ P :=
    Submodule.span_le.2 fun f hf => hf
  let L : P →ₗ[ℂ] ((∀ i, Y i) → ℂ) :=
    { toFun := fun f y => (f : (∀ i, X i) → ℂ) (fun i => (y i : X i))
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfP : ∀ i x, (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) ∈ S i := f.2
    have key : ∀ A : Finset ι, ∀ x : ∀ i, X i, (∀ j ∉ A, x j ∈ Y j) →
        (f : (∀ i, X i) → ℂ) x = 0 := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro x hx
        have h0 := congrFun hf (fun j => ⟨x j, hx j (by simp)⟩)
        simpa [L] using h0
      | @insert i A hiA ih =>
        intro x hx
        have hg : (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) = 0 := by
          refine hY i _ (hfP i x) ?_
          intro y hy
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst hji
            simpa using hy
          · rw [Function.update_of_ne hji]
            exact hx j (by simp [hji, hj])
        have h1 := congrFun hg (x i)
        simpa using h1
    apply Subtype.ext
    funext x
    exact key Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj)
  have : FiniteDimensional ℂ P := Module.Finite.of_injective L hL
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
