import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.InvBaseChange

open TensorProduct

namespace PI.CoefExt

section

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W W₂ : Type} [AddCommGroup W] [Module K W]
  [AddCommGroup W₂] [Module K W₂]

theorem coord_baseChange {ι : Type} [DecidableEq ι] (b : Module.Basis ι K L) (f : W →ₗ[K] W₂) (x : L ⊗[K] W) :
    equivFinsuppOfBasisLeft b (f.baseChange L x)
      = Finsupp.mapRange f f.map_zero (equivFinsuppOfBasisLeft b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
    ext i
    simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext i
    simp

end

theorem invBaseChange : InvBaseChange := by
  intro LL LL' _ _ _ W _ _ G T
  classical
  set V : Submodule LL W := ⨅ g, LinearMap.ker (T g - LinearMap.id) with hV
  have memV : ∀ w, w ∈ V ↔ ∀ g, T g w = w := by
    intro w
    simp [hV, Submodule.mem_iInf, sub_eq_zero]
  obtain ⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι LL LL') :=
    ⟨_, ⟨Module.Free.chooseBasis LL LL'⟩⟩
  have hinj : Function.Injective (V.subtype.baseChange LL') := by
    intro z₁ z₂ h
    have h' := congrArg (equivFinsuppOfBasisLeft b) h
    rw [coord_baseChange b V.subtype z₁,
      coord_baseChange b V.subtype z₂] at h'
    apply (equivFinsuppOfBasisLeft b).injective
    ext i
    have := congrArg (fun c => c i) h'
    simpa using this
  have hrange : (⨅ g, LinearMap.ker ((T g).baseChange LL' - LinearMap.id) :
      Submodule LL' (LL' ⊗[LL] W)) = LinearMap.range (V.subtype.baseChange LL') := by
    apply le_antisymm
    · intro x hx
      have hfix : ∀ g, (T g).baseChange LL' x = x := by
        intro g
        have := (Submodule.mem_iInf _).1 hx g
        simpa [sub_eq_zero] using this
      have hc : ∀ i, equivFinsuppOfBasisLeft b x i ∈ V := by
        intro i
        rw [memV]
        intro g
        have := congrArg (fun c => c i) (coord_baseChange b (T g) x)
        simp only [hfix g, Finsupp.mapRange_apply] at this
        exact this.symm
      rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply]
      unfold Finsupp.sum
      refine Submodule.sum_mem _ fun i _ => ?_
      exact LinearMap.mem_range.2 ⟨b i ⊗ₜ ⟨_, hc i⟩, by simp⟩
    · rintro _ ⟨z, rfl⟩
      rw [Submodule.mem_iInf]
      intro g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a v =>
        have hv := (memV v).1 v.2 g
        simp [hv]
      | add x y hx hy => simp only [map_add, hx, hy]
  rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

end PI.CoefExt
