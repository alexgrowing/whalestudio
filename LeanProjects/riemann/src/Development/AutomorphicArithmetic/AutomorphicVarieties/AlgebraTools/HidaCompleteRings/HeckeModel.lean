import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
open IsLocalRing UpperTheory.V.Hi

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] (Y : Submodule A M) (op : ι → Module.End A M), CommOn Y op → ∃ (T : Type) (_ : CommRing T) (_ : Algebra A T) (j : T →ₐ[A] Module.End A Y) (t : ι → T), Function.Injective j ∧ j.range = heckeAlg Y op ∧ (∀ i, Restr (j (t i)) (op i)) ∧ Algebra.adjoin A (Set.range t) = ⊤ ∧ (IsNoetherianRing A → Module.Finite A Y → Module.Finite A T) := by
  intro A M ι _ _ _ Y op h
  have key : ∀ s ∈ {t : Module.End A Y | ∃ i, Restr t (op i)},
      ∀ t ∈ {t : Module.End A Y | ∃ i, Restr t (op i)}, s * t = t * s := by
    rintro s ⟨i, hi⟩ t ⟨j, hj⟩
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (s (t y) : M) = t (s y)
    rw [hi, hj, hj, hi]
    exact h.2 i j y y.2
  have hc : ∀ a b : heckeAlg Y op, a * b = b * a := fun a b =>
    (Algebra.adjoinCommSemiringOfComm A key).mul_comm a b
  let t : ι → heckeAlg Y op := fun i =>
    ⟨(op i).restrict (h.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩
  have htop : Algebra.adjoin A (Set.range t) = ⊤ := by
    have h1 : Set.range t = ((↑) : heckeAlg Y op → Module.End A Y) ⁻¹'
        {t : Module.End A Y | ∃ i, Restr t (op i)} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, fun _ => rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext (LinearMap.ext fun y => Subtype.ext (hi y).symm)⟩
    rw [h1]
    exact Algebra.adjoin_adjoin_coe_preimage
  have hfin : IsNoetherianRing A → Module.Finite A Y → Module.Finite A (heckeAlg Y op) := by
    intro _ _
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := Y)
    let f : heckeAlg Y op →ₗ[A] (Fin n → Y) :=
      { toFun := fun t i => (t : Module.End A Y) (s i)
        map_add' := fun a b => by ext i; simp
        map_smul' := fun a b => by ext i; simp }
    have hf : Function.Injective f := by
      intro a b hab
      refine Subtype.ext (LinearMap.ext_on_range hs fun i => ?_)
      exact congrFun hab i
    exact Module.Finite.of_injective f hf
  exact ⟨heckeAlg Y op, { (inferInstance : Ring (heckeAlg Y op)) with mul_comm := hc },
    (inferInstance : Algebra A (heckeAlg Y op)), (heckeAlg Y op).val, t, Subtype.val_injective,
    Subalgebra.range_val _, fun i _ => rfl, htop, hfin⟩
