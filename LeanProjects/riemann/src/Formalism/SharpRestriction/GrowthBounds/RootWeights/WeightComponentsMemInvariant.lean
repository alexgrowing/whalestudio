import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantOrthogonalityHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightComponentsMemInvariant

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem weight_components_mem_invariant [CharZero K] (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (s : Finset (Fin n → ℤ)) : ∀ f : (Fin n → ℤ) → V, (∀ mu ∈ s, f mu ∈ weightSp E mu) →
      ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W :=
  _root_.UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant E W hW s

theorem weightSpace_independent [CharZero K] (E : GLOps n K V) : iSupIndep (weightSp E) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv h0 i hi
  have := weight_components_mem_invariant E ⊥ (fun a x hx => by simp [(Submodule.mem_bot K).1 hx]) s v hv (by simp [h0]) i hi
  simpa using this

variable (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)

@[simp] theorem restricted_operator_coe (a b : Fin n) (x : W) : ((restrictStableOperators E W h a b x : W) : V) = E a b x := rfl

theorem restricted_mem_weightSpace_iff (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isHWV_iff (lam : Fin n → ℤ) (v : W) : IsHWV (restrictStableOperators E W h) lam v ↔ IsHWV E lam (v : V) := by
  unfold IsHWV
  rw [restricted_mem_weightSpace_iff]
  refine and_congr (by simp) (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun _ => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isGLRep [CharZero K] (hE : IsGLRep E) : IsGLRep (restrictStableOperators E W h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    ext x
    have h1 := congrArg (fun f : Module.End K V => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restricted_operator_coe]
    rw [h1]
    split_ifs <;> simp
  · intro x
    obtain ⟨W0, hfd, hx0, hst⟩ := hE.2.1 (x : V)
    refine ⟨W0.comap W.subtype, ?_, hx0, fun a b y hy => hst a b _ hy⟩
    have h1 : FiniteDimensional K ((W0.comap W.subtype).map W.subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective W.subtype W.injective_subtype (W0.comap W.subtype)).symm
  · rw [eq_top_iff]
    intro x _
    have hx : (x : V) ∈ ⨆ mu, weightSp E mu := by rw [hE.2.2]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
    have hmem := weight_components_mem_invariant E W (fun a => h a a) f.support f (fun mu _ => hf mu)
      (by have : ∑ mu ∈ f.support, f mu = (x : V) := hsum
          rw [this]; exact x.2)
    have hx2 : x = ∑ mu ∈ f.support.attach, (⟨f mu.1, hmem mu.1 mu.2⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only
      rw [Finset.sum_attach f.support (fun mu => f mu)]
      exact hsum.symm
    rw [hx2]
    refine Submodule.sum_mem _ fun mu _ => ?_
    exact Submodule.mem_iSup_of_mem mu.1 ((restricted_mem_weightSpace_iff E W h mu.1 _).2 (hf mu.1))

end Formalism.MainNotions.G.GLWeightTheory
