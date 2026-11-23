import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_dual_pairing {R : Type} [CommRing R] {M N : Type 1}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Projective R N] (u : M ⊗[R] N)
    (h : ∀ (x : Module.Dual R M) (y : Module.Dual R N),
      TensorProduct.lift ((LinearMap.mul R R).compl₁₂ x y) u = 0) : u = 0 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
  obtain ⟨s', hs'⟩ := Module.Projective.out (R := R) (P := N)
  have key : ∀ (w : M ⊗[R] N) (c : M) (c' : N),
      finsuppTensorFinsupp' R M N (TensorProduct.map s s' w) (c, c') =
        TensorProduct.lift ((LinearMap.mul R R).compl₁₂ ((Finsupp.lapply c).comp s)
          ((Finsupp.lapply c').comp s')) w := by
    intro w c c'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply]
    | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw]
  have h0 : TensorProduct.map s s' u = 0 := by
    apply (finsuppTensorFinsupp' R M N).injective
    rw [map_zero]
    ext ⟨c, c'⟩
    rw [key]
    exact h _ _
  have hl : (Finsupp.linearCombination R id).comp s = LinearMap.id := LinearMap.ext hs
  have hl' : (Finsupp.linearCombination R id).comp s' = LinearMap.id := LinearMap.ext hs'
  have : u = TensorProduct.map (Finsupp.linearCombination R id) (Finsupp.linearCombination R id)
      (TensorProduct.map s s' u) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hl, hl', TensorProduct.map_id,
      LinearMap.id_apply]
  rw [this, h0, map_zero]

theorem tensor_mem_of_dualAnnihilator : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R M] [Module.Projective R N] (F : Submodule R M) (F' : Submodule R N), (∃ C, IsCompl F C) → (∃ C, IsCompl F' C) → (∀ c : M, (∀ h ∈ F.dualAnnihilator, h c = 0) → c ∈ F) ∧ ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N), (∀ x ∈ F.dualAnnihilator, ∀ y ∈ F'.dualAnnihilator, ∑ k, x (a k) * y (b k) = 0) → ∃ (a₁ : Fin n → M) (b₁ : Fin n → N), (∀ k, a₁ k ∈ F) ∧ (∀ k, b₁ k ∈ F') ∧ ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0 := by
  intro R _ M N _ _ _ _ _ _ F F' ⟨C, hC⟩ ⟨C', hC'⟩
  set e : M →ₗ[R] M := C.subtype.comp (C.linearProjOfIsCompl F hC.symm) with he
  set e' : N →ₗ[R] N := C'.subtype.comp (C'.linearProjOfIsCompl F' hC'.symm) with he'
  have eF : ∀ f ∈ F, e f = 0 := fun f hf => by
    rw [he, LinearMap.comp_apply, show C.linearProjOfIsCompl F hC.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC.symm ⟨f, hf⟩, map_zero]
  have eF' : ∀ f ∈ F', e' f = 0 := fun f hf => by
    rw [he', LinearMap.comp_apply, show C'.linearProjOfIsCompl F' hC'.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC'.symm ⟨f, hf⟩, map_zero]
  have sub : ∀ m, m - e m ∈ F := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC.symm, LinearMap.mem_ker, map_sub, he,
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have sub' : ∀ m, m - e' m ∈ F' := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC'.symm, LinearMap.mem_ker, map_sub, he',
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have ann : ∀ x : Module.Dual R M, x.comp e ∈ F.dualAnnihilator := fun x => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF f hf]
  have ann' : ∀ y : Module.Dual R N, y.comp e' ∈ F'.dualAnnihilator := fun y => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF' f hf]
  refine ⟨fun c hc => ?_, fun n a b hab => ?_⟩
  · have : e c = 0 := (Module.forall_dual_apply_eq_zero_iff R (e c)).mp fun x => hc _ (ann x)
    simpa [this] using sub c
  · refine ⟨fun k => a k - e (a k), fun k => b k - e' (b k), fun k => sub _, fun k => sub' _, ?_⟩
    simp only [sub_sub_cancel]
    apply tensor_eq_zero_of_forall_dual_pairing
    intro x y
    simp only [map_sum, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    exact hab _ (ann x) _ (ann' y)

end GlobalTheory
