import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem admissible_exact_sequence (hD : DinvExact) {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) {L : Type} [Field L] [Algebra F L] {e : ℕ} (hB : Bound σ L e)
    {U V W : Type} [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W)
    (i : U →ₗ[L] V) (p : V →ₗ[L] W) (hi : Inter ρU ρV i) (hp : Inter ρV ρW p)
    (inj : Function.Injective i) (ex : Function.Exact i p) (surj : Function.Surjective p)
    (hA : admitted σ e ρV) :
    admitted σ e ρU ∧ admitted σ e ρW ∧
      (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρW := by
  obtain ⟨fU, bU⟩ := hB U ρU
  obtain ⟨fV, -⟩ := hB V ρV
  obtain ⟨fW, bW⟩ := hB W ρW
  obtain ⟨hle, hdim⟩ := hD F G B σ L U V W ρU ρV ρW i p hi hp inj ex fV
  have hmono := Submodule.finrank_mono hle
  have hrank : finrank L V = finrank L U + finrank L W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker p
    rw [LinearMap.range_eq_top.mpr surj, finrank_top, LinearMap.exact_iff.mp ex,
      LinearMap.finrank_range_of_inj inj] at h1
    omega
  unfold admitted at hA ⊢
  rw [hrank, mul_add] at hA
  have h2 : finrank L (Dinv σ ρU) = e * finrank L U := by omega
  have h3 : finrank L (Dinv σ ρW) = e * finrank L W := by omega
  refine ⟨h2, h3, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  omega

theorem UpperTheory.Gal.crystallineComparison.admissibleExact_of_dualInvariantExact :
    DinvExact → AdmExact := by
  intro hD
  unfold AdmExact
  intro F G B _ _ _ _ σ L _ _ e hB V W _ _ _ _ _ _ _ _ _ _ ρ ρ' f hf
  refine ⟨fun inj hA => ?_, fun surj hA => ?_⟩
  · let ρQ : Representation L G (W ⧸ LinearMap.range f) :=
      { toFun := fun g => (LinearMap.range f).mapQ (LinearMap.range f) (ρ' g) (by
          rintro _ ⟨v, rfl⟩
          exact ⟨ρ g v, hf g v⟩)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro g h
          ext w
          simp [map_mul] }
    have hQ : UpperTheory.Gal.crystallineComparison.Inter ρ' ρQ (LinearMap.range f).mkQ := fun g w => rfl
    exact (admissible_exact_sequence hD σ hB ρ ρ' ρQ f (LinearMap.range f).mkQ hf hQ inj
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _) hA).1
  · have hK : ∀ (g : G) (x : LinearMap.ker f), ρ g x ∈ LinearMap.ker f := by
      intro g x
      rw [LinearMap.mem_ker, hf g x, LinearMap.mem_ker.mp x.2, map_zero]
    let ρK : Representation L G (LinearMap.ker f) :=
      { toFun := fun g => LinearMap.codRestrict (LinearMap.ker f)
          ((ρ g).comp (LinearMap.ker f).subtype) (hK g)
        map_one' := by
          ext x
          simp
        map_mul' := by
          intro g h
          ext x
          simp only [map_mul, Module.End.mul_apply]
          rfl }
    have hKi : UpperTheory.Gal.crystallineComparison.Inter ρK ρ (LinearMap.ker f).subtype := fun g x => rfl
    obtain ⟨-, hW, hmap⟩ := admissible_exact_sequence hD σ hB ρK ρ ρ' (LinearMap.ker f).subtype f hKi hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) surj hA
    exact ⟨hW, hmap⟩
