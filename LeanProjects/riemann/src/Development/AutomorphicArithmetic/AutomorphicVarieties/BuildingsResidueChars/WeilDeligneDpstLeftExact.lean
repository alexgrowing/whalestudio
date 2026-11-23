import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem tensV_eq_rT {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem UpperTheory.weilDeligne_dpst_leftExact :
    UpperTheory.V.Af.Wd.DLeft := by
  intro l _ P K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hex0
  have hex : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex0
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((f.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hfi
  refine ⟨fun x y hxy => Subtype.ext (hinj ?_), fun y => ⟨fun hy => ?_, ?_⟩⟩
  · rw [← tensV_eq_rT, ← tensV_eq_rT]
    exact congrArg Subtype.val hxy
  · have h0 : tensV P p (y : V ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val hy
    rw [tensV_eq_rT] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P f z = y := by rw [tensV_eq_rT]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
    have hzD : z ∈ Dpst P ρ' := by
      refine (mem_Dpst P ρ').mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rT, ← tensV_eq_rT, tensV_stRep P ρ' ρ f hf, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    show tensV P p (tensV P f x.1) = 0
    rw [tensV_eq_rT, tensV_eq_rT]
    exact (hexT _).mpr ⟨x.1, rfl⟩
